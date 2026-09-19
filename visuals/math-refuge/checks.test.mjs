import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {SHOTS,smoothProgress,fadeAt,advanceShot} from './camera-paths.js';
import * as Three from '../3d/vendor/three.module.js';
import {LectureClock,boardSlot,boardHeights} from './lecture-state.js';
import {configureCameraInput,DEFAULT_ROTATION} from './camera-input.js';
import {displayProfile,boardFraming,readingFormulaWidth} from './display-profile.js';
import {elevation,coastline,shoreline,canPlant,slope,seaLevel} from './landscape-shape.js';
import {createHash} from 'node:crypto';

test('seven finite camera chapters with seminar and ocean views',()=>{
  assert.equal(SHOTS.length,7);assert(SHOTS.some(s=>s.lecture));assert(SHOTS.some(s=>s.name==='海景露台'));
  for(const shot of SHOTS){
    assert(shot.duration>=20);assert(shot.fov>30&&shot.fov<70);
    for(const points of [shot.positions,shot.targets]){
      const curve=new Three.CatmullRomCurve3(points.map(p=>new Three.Vector3(...p)));
      for(let i=0;i<=100;i++)assert(curve.getPointAt(smoothProgress(i/100)).toArray().every(Number.isFinite));
    }
  }
  assert.equal(fadeAt(0),1);assert.equal(fadeAt(.5),0);assert(Math.abs(fadeAt(1)-1)<1e-9);
  const wrap=advanceShot(6,27.98,.05,1);assert.equal(wrap.index,0);assert(wrap.time>=0&&wrap.time<.1);
  assert.deepEqual(advanceShot(0,1,-5,1),{index:0,time:1});
});

test('all page and JavaScript local asset references resolve',async()=>{
  const root=new URL('./',import.meta.url);
  for(const file of ['index.html','app.js','scene.js','camera-paths.js','lecture.js','lecture-state.js','chalk-reader.js','display-profile.js','surface-materials.js','landscape.js','landscape-shape.js']){
    const code=await fs.readFile(new URL(file,root),'utf8');
    const links=file.endsWith('.html') ? [...code.matchAll(/(?:src|href)="([^"#]+)"/g)].map(m=>m[1]) : [...code.matchAll(/(?:from\s+|import\()['"](\.[^'"]+)['"]/g)].map(m=>m[1]);
    for(const link of links){if(link.startsWith('http'))continue;await fs.access(new URL(link.split('?')[0],root));}
  }
  for(const name of ['wood-color.jpg','wood-normal.jpg','wood-rough.jpg','stone-color.jpg','stone-normal.jpg','stone-rough.jpg','waternormals.jpg'])assert((await fs.stat(new URL('assets/'+name,root))).size>1000);
  async function scan(directory){
    for(const entry of await fs.readdir(directory,{withFileTypes:true})){
      const file=new URL(entry.name+(entry.isDirectory()?'/':''),directory);
      if(entry.isDirectory()){await scan(file);continue;}
      if(!entry.name.endsWith('.js'))continue;
      const code=(await fs.readFile(file,'utf8')).replace(/\/\*[\s\S]*?\*\//g,'');
      for(const match of code.matchAll(/from\s+['"]([^'"]+)['"]/g)){
        if(match[1]==='three')continue;
        const target=match[1].startsWith('three/addons/')?new URL(match[1].replace('three/addons/','vendor/'),root):new URL(match[1].split('?')[0],file);
        await fs.access(target);
      }
    }
  }
  await scan(root);
  const html=await fs.readFile(new URL('index.html',root),'utf8');
  const ids=new Set([...html.matchAll(/id="([^"]+)"/g)].map(m=>m[1]));
  const app=await fs.readFile(new URL('app.js',root),'utf8');
  for(const file of ['app.js','chalk-reader.js']){
    const code=await fs.readFile(new URL(file,root),'utf8');
    for(const match of code.matchAll(/\$\('([^']+)'\)/g))assert(ids.has(match[1]),'Missing element '+match[1]);
  }
});

test('scene assembly creates valid model buffers without a browser or GPU',async()=>{
  const coreURL=new URL('../3d/vendor/three.module.js',import.meta.url).href;
  const asModule=source=>'data:text/javascript;base64,'+Buffer.from(source).toString('base64');
  async function inlineAddon(file){
    let source=await fs.readFile(new URL(file,import.meta.url),'utf8');
    source=source.replaceAll("from 'three'",`from '${coreURL}'`);
    if(file.startsWith('./landscape.js'))source=source.replace(`import * as THREE from '${coreURL}';`,'const THREE=globalThis.__retreatTestThree;').replace('./landscape-shape.js',new URL('./landscape-shape.js',import.meta.url).href);
    return asModule(source);
  }
  let source=await fs.readFile(new URL('./scene.js',import.meta.url),'utf8');
  source=source.replace("import * as THREE from 'three';",'const THREE=globalThis.__retreatTestThree;');
  for(const file of ['./vendor/geometries/RoundedBoxGeometry.js','./vendor/objects/Water.js','./vendor/objects/Sky.js','./surface-materials.js?v=5-mobile','./landscape.js?v=6-landscape'])source=source.replace(file,await inlineAddon(file));
  const calls=[];let clippedFragments=0;
  globalThis.__retreatTestThree={...Three,
    TextureLoader:class{async loadAsync(){const texture=new Three.Texture();texture.image={width:256,height:256};return texture;}},
    PMREMGenerator:class{fromScene(){return {texture:new Three.Texture(),dispose(){}};}dispose(){}}
  };
  globalThis.document={createElement:()=>({width:0,height:0,getContext:()=>({fillRect(){},fillText(text){calls.push(text);},save(){},restore(){},translate(){},rotate(){},beginPath(){},moveTo(){},lineTo(){},closePath(){},clip(){clippedFragments++;},drawImage(){}})})};
  try{
    const {createRetreat}=await import(asModule(source));
    const scene=new Three.Scene();
    const result=await createRetreat({capabilities:{getMaxAnisotropy:()=>8}},scene,()=>{});
    assert(result.water.isMesh);assert(result.ocean.isMesh);assert(result.sculpture.isMesh);assert(scene.environment);
    assert.equal(scene.getObjectByName('Ocean conference table').userData.seats,14);
    assert(scene.getObjectByName('Conference entrance sign').isMesh);
    assert.equal(result.ocean.position.y,result.site.seaLevel);
    for(const z of [-14,0,14]){
      assert(result.site.elevation(28,z)>result.site.seaLevel);
      assert(result.site.elevation(result.site.coastline(z)+15,z)<result.site.seaLevel);
    }
    let instances=0,triangles=0;
    for(const object of scene.children){
      if(!object.geometry)continue;
      assert([...object.geometry.attributes.position.array].every(Number.isFinite));
      if(object.isInstancedMesh){assert([...object.instanceMatrix.array].every(Number.isFinite));instances+=object.count;}
      triangles+=(object.geometry.index?.count || object.geometry.attributes.position.count)/3*(object.isInstancedMesh?object.count:1);
    }
    console.log(JSON.stringify({sceneObjects:scene.children.length,instances,triangles,forestTrees:result.landscape.plantings.length}));
    assert(instances>3000);assert(triangles<900000,`Complete modeled vegetation remains within the 900k scene budget: ${triangles}`);
    assert(scene.children.filter(o=>o.isMesh).length<240,'Spatial instancing must bound model draw batches');
    for(const name of ['Continuous mountain ridges','Detailed coastal terrain','Olive leaf canopies','Palm fronds','Fern understory','Coastal grasses','Weathered coastal outcrops'])assert(scene.getObjectByName(name),name);
    assert(!scene.children.some(o=>o.geometry?.type==='ConeGeometry'));
    assert(result.landscape.plantings.length>150);
    for(const [x,y,z] of result.landscape.plantings){assert(canPlant(x,z));assert.equal(y,elevation(x,z));}
    // Execute shader-patching callbacks against the pinned Three shader source.
    // This catches missing replacement hooks, but is not a GPU compile test.
    for(const name of ['Continuous mountain ridges','Olive leaf canopies']){
      const m=scene.getObjectByName(name).material,shader={uniforms:{},vertexShader:Three.ShaderLib.standard.vertexShader,fragmentShader:Three.ShaderLib.standard.fragmentShader};
      m.onBeforeCompile(shader);assert(Object.keys(shader.uniforms).length>0);assert(!shader.fragmentShader.includes('undefined'));assert(shader.vertexShader.includes(name.startsWith('Continuous')?'vTerrainPoint=position':'float sway='));
    }
    result.landscape.update(.016);result.landscape.update(-1);
    const coast=scene.getObjectByName('Detailed coastal terrain').geometry.attributes.position;
    for(let i=0;i<coast.count;i++){
      const x=coast.getX(i),z=coast.getZ(i);if(Math.abs(x)!==90&&Math.abs(z)!==90)continue;
      const vertical=Math.abs(x)===90,q=vertical?z:x,lo=Math.floor(q/6)*6,t=(q-lo)/6;
      const expected=vertical?Three.MathUtils.lerp(elevation(x,lo),elevation(x,lo+6),t):Three.MathUtils.lerp(elevation(lo,z),elevation(lo+6,z),t);
      assert(Math.abs(coast.getY(i)-expected)<.00002,'Fine and coarse terrain edges must not crack');
    }
    assert(result.materials.pale.normalMap.isDataTexture);assert(result.materials.steel.roughnessMap.isDataTexture);
    assert(result.materials.pale.normalMap.generateMipmaps);assert(result.materials.timber.normalMap);
    assert(calls.includes('NS 方程 · 存在性与光滑性'));assert(calls.includes('Hodge 猜想 ？'));assert(calls.includes('数学难民营'));
    assert(calls.includes('NS'));assert.equal(clippedFragments,12);
    for(const name of ['NS conjecture blackboard','Hodge conjecture blackboard','Entrance lintel sign','Entrance wayfinding sign'])assert(scene.getObjectByName(name)?.isMesh,name);
    assert(!calls.some(text=>text.includes('已解决')));
    assert(result.water.material.uniforms.time);assert.equal(typeof result.lighting,'function');
    result.lighting(0,true);result.lighting(100,true);result.dispose();
    assert.deepEqual(result.ocean.material.uniforms.sunDirection.value.toArray(),result.water.material.uniforms.sunDirection.value.toArray());
  }finally{delete globalThis.__retreatTestThree;delete globalThis.document;}
});

test('continuous ridges, level foundations and actual waterline stay consistent',()=>{
  for(const [x,z] of [[0,0],[28,0],[37,8],[-15,12]])assert.equal(elevation(x,z),-2.1);
  for(let z=-600;z<=600;z+=5){
    assert(Math.abs(elevation(shoreline(z),z)-seaLevel)<.0001);
    assert(shoreline(z)>coastline(z)-4&&shoreline(z)<coastline(z)+11);
    assert(!canPlant(coastline(z)+15,z));
  }
  for(let x=-500;x<100;x+=8)for(let z=-500;z<200;z+=8){assert(Number.isFinite(elevation(x,z)));assert(Number.isFinite(slope(x,z)));assert(Math.abs(elevation(x+.001,z)-elevation(x,z))<.1);}
  assert(elevation(-260,-180)>60);assert(!canPlant(28,0));
});

test('locally served landscape photographs match their CC0 source manifest',async()=>{
  const assets=new URL('./assets/',import.meta.url),manifest=JSON.parse(await fs.readFile(new URL('landscape-sources.json',assets),'utf8'));
  assert.equal(manifest.length,6);let total=0;
  for(const item of manifest){const bytes=await fs.readFile(new URL(item.file,assets));assert.equal(createHash('sha256').update(bytes).digest('hex'),item.sha256);assert.equal(bytes.length,item.bytes);assert.equal(item.license,'CC0-1.0');assert(item.downloadURL.startsWith('https://dl.polyhaven.org/'));total+=bytes.length;}
  assert(total<6500000);console.log(JSON.stringify({landscapeTextureBytes:total}));
});

test('three pairs alternate six slots, erase reused boards and wrap lecture pages',()=>{
  assert.deepEqual(Array.from({length:6},(_,i)=>boardSlot(i)),[0,2,4,1,3,5]);
  for(let value=0;value<=1;value+=.05){const [a,b]=boardHeights(value);assert(Math.abs(a+b-5.15)<1e-9);assert(a>=1.45&&a<=3.7);assert(b>=1.45&&b<=3.7);}
  const clock=new LectureClock(65),phases=new Set(),slots=new Set();
  for(let step=0;step<3000;step++){clock.update(.1);phases.add(clock.phase);slots.add(clock.active);assert(clock.progress>=0&&clock.progress<=1);}
  assert.deepEqual([...phases].sort(),['erase','hold','lift','write']);assert.equal(slots.size,6);
  clock.select(64);clock.next();assert.equal(clock.page,0);clock.next(-1);assert.equal(clock.page,64);
  clock.select(4);clock.startWrite();assert.equal(clock.slots[clock.active].page,4);assert.equal(clock.slots[clock.active].progress,0);
  const elapsed=clock.elapsed;clock.update(-1);assert.equal(clock.elapsed,elapsed);
});

test('65 local SVG pages preserve notebook formula content and stay within the board',async()=>{
  const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/pages.json',import.meta.url),'utf8'));
  assert.equal(pages.length,65);assert(pages.some(p=>p.source.startsWith('Hodge')));assert(pages.some(p=>p.source.startsWith('Leray')));
  for(const page of pages){
    const svg=await fs.readFile(new URL(page.asset,import.meta.url),'utf8');
    const formula=await fs.readFile(new URL(page.formulaAsset,import.meta.url),'utf8');
    assert(formula.includes('<path'));assert(!formula.includes('data-mjx-error'));assert(page.formulaEm>0);
    assert(svg.includes('<path'));assert(!svg.includes('data-mjx-error'));assert(!svg.includes('<script'));
    assert(!/(?:href|src)="https?:/.test(svg));assert(page.tex.length>0);
    for(const [x,y,w,h] of page.rows){assert(x>=0&&y>=0);assert(x+w<=1536&&y+h<=640);}
  }
  assert(pages.some(p=>p.tex.includes('\\delta_1\\delta_2+\\delta_2\\delta_1=0')));
  assert(pages.some(p=>p.tex.includes('\\operatorname{Gr}_F')));
  const html=await fs.readFile(new URL('./index.html',import.meta.url),'utf8');
  assert.equal([...html.matchAll(/data-shot="\d"/g)].length,SHOTS.length);
  for(let i=0;i<3;i++){assert(html.includes(`id="boardLift${i}"`));assert(html.includes(`id="boardSwap${i}"`));}
});

test('phone rendering preserves Retina pixels and AA within a bounded budget',()=>{
  const portrait=displayProfile(390,844,3),landscape=displayProfile(844,390,3);
  assert.equal(portrait.pixelRatio,3);assert.equal(portrait.samples,4);assert(portrait.direct);assert(!portrait.bloom);assert(portrait.shadows);
  assert.equal(portrait.pixelRatio,landscape.pixelRatio);assert.equal(portrait.compact,landscape.compact);
  for(const [w,h,dpr] of [[320,568,2],[430,932,3],[768,1024,2],[1440,900,2],[3840,2160,3]]){
    const p=displayProfile(w,h,dpr);assert(w*h*p.pixelRatio*p.pixelRatio<=6000000.01);assert(p.pixelRatio<=dpr);assert(p.samples>0);
  }
  assert(!displayProfile(390,844,3,'high',4,0).direct,'Use compositor MSAA when native MSAA is absent');
  assert.equal(displayProfile(390,844,3,'high',2,0).samples,2);
  assert.equal(displayProfile(390,844,3,'high',0,0).samples,0);
  const framing=boardFraming(390/844),visibleWidth=2*framing.distance*Math.tan(57*Math.PI/360)*(390/844);
  assert(framing.single);assert(5.3/visibleWidth>.8);assert(framing.distance<5.9/(390/844));
  assert(readingFormulaWidth(22,24)>=528,'Long formulas scroll instead of shrinking below the selected font size');
});

test('classroom assembles six independent boards and survives writing, erasing and manual lifts',async()=>{
  const core=new URL('../3d/vendor/three.module.js',import.meta.url).href;
  const state=new URL('./lecture-state.js',import.meta.url).href;
  let source=await fs.readFile(new URL('./lecture.js',import.meta.url),'utf8');
  source=source.replace("from 'three'",`from '${core}'`).replace('./lecture-state.js?v=3-coast',state);
  const originalFetch=globalThis.fetch,originalImage=globalThis.Image,originalDocument=globalThis.document;
  const contexts=[];
  globalThis.document={createElement:()=>({width:0,height:0,getContext(){
    const ctx={drawImage(){},fillRect(){},save(){},restore(){},beginPath(){},rect(){},clip(){}};contexts.push(ctx);return ctx;
  }})};
  globalThis.Image=class{set src(value){this.url=value;queueMicrotask(()=>this.onload());}};
  globalThis.fetch=async()=>({ok:true,json:async()=>JSON.parse(await fs.readFile(new URL('./assets/chalk/pages.json',import.meta.url),'utf8'))});
  try{
    const {createLecture}=await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
    const scene=new Three.Scene(),lecture=await createLecture(scene,{capabilities:{getMaxAnisotropy:()=>8}});
    const boards=scene.children.filter(o=>o.name.startsWith('Sliding chalkboard'));
    assert.equal(boards.length,6);assert.equal(new Set(boards.map(b=>b.children[0].material.map.uuid)).size,6);
    const phases=new Set();
    for(let i=0;i<3500;i++){lecture.update(.1);phases.add(lecture.clock.phase);if(i%10===0)await Promise.resolve();}
    assert(phases.has('write'));assert(phases.has('erase'));assert(phases.has('lift'));
    lecture.playing=false;const time=lecture.clock.elapsed;lecture.update(.1);assert.equal(lecture.clock.elapsed,time);
    const uploads=boards.map(b=>b.children[0].material.map.version);
    for(let i=0;i<50;i++)lecture.update(.1);
    assert.deepEqual(boards.map(b=>b.children[0].material.map.version),uploads,'Unchanged boards must not re-upload textures');
    lecture.lift(0,1);for(let i=0;i<50;i++)lecture.update(.1);
    assert(Math.abs(boards[0].position.y-3.7)<.001);assert(Math.abs(boards[1].position.y-1.45)<.001);
    lecture.select(64);await Promise.resolve();lecture.staticPage();lecture.update(.1,true);
    assert.equal(lecture.clock.page,64);assert.equal(lecture.clock.slots[lecture.clock.active].progress,1);
    assert(!scene.getObjectByName('Writing chalk').visible);assert(!scene.getObjectByName('Moving blackboard eraser').visible);
    for(const board of boards)assert(board.position.toArray().every(Number.isFinite));
    assert(lecture.focus().toArray().every(Number.isFinite));lecture.dispose();
  }finally{globalThis.fetch=originalFetch;globalThis.Image=originalImage;globalThis.document=originalDocument;}
});

test('vector chalk reader respects dismissal and keeps text independent of WebGL',async()=>{
  const originalDocument=globalThis.document,originalWidth=globalThis.innerWidth,originalHeight=globalThis.innerHeight;
  const html=await fs.readFile(new URL('./index.html',import.meta.url),'utf8');
  const elements=new Map([...html.matchAll(/id="([^"]+)"/g)].map(([,id])=>[id,{
    hidden:['chalkReader','lecturePanel'].includes(id),style:{},value:id==='readerFont'?'24':'',attributes:{},events:{},
    addEventListener(type,handler){this.events[type]=handler;},setAttribute(k,v){this.attributes[k]=v;},click(){this.events.click?.();}
  }]));
  globalThis.document={getElementById:id=>elements.get(id)};globalThis.innerWidth=390;globalThis.innerHeight=844;
  const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/pages.json',import.meta.url),'utf8'));
  const lecture={pages,clock:{page:0},playing:true};
  const source=(await fs.readFile(new URL('./chalk-reader.js',import.meta.url),'utf8')).replace('./display-profile.js?v=5-mobile',new URL('./display-profile.js',import.meta.url).href);
  try{
    const {createChalkReader}=await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
    const reader=createChalkReader(lecture),panel=elements.get('chalkReader');
    reader.chapter(true);assert(!panel.hidden);assert(elements.get('readerFormula').src.includes('formula-001.svg'));assert.equal(elements.get('readerExplanation').textContent,pages[0].text);
    elements.get('readerClose').click();reader.chapter(true);assert(panel.hidden,'Do not reopen dismissed reader on same chapter');
    reader.chapter(false);reader.chapter(true,false);assert(panel.hidden,'Do not cover the manually opened board control panel');
    elements.get('readerOpen').click();assert(!panel.hidden);
    elements.get('readerFont').value='30';elements.get('readerFont').events.input();assert.equal(elements.get('readerFormula').style.width,readingFormulaWidth(pages[0].formulaEm,30)+'px');
    lecture.clock.page=1;reader.update();assert.equal(elements.get('readerExplanation').textContent,pages[1].text);
    reader.close();assert(panel.hidden);
  }finally{globalThis.document=originalDocument;globalThis.innerWidth=originalWidth;globalThis.innerHeight=originalHeight;}
});

test('mouse and touch rotation are slower, with zoom and pan preserved',async()=>{
  const core=new URL('../3d/vendor/three.module.js',import.meta.url).href;
  const source=(await fs.readFile(new URL('../3d/vendor/OrbitControls.js',import.meta.url),'utf8')).replace("from 'three'",`from '${core}'`);
  const {OrbitControls}=await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
  for(const pointerType of ['mouse','touch']){
    const camera=new Three.PerspectiveCamera(60,1,.1,1000);camera.position.set(0,0,10);
    const controls=new OrbitControls(camera);let pointer,capture;
    const element={clientHeight:800,addEventListener(type,handler,options){assert.equal(type,'pointerdown');pointer=handler;capture=options.capture;},removeEventListener(){}};
    controls.domElement=element;
    const zoom=controls.zoomSpeed,pan=controls.panSpeed,input=configureCameraInput(controls,element);
    assert(capture);pointer({pointerType});
    assert.equal(controls.rotateSpeed,DEFAULT_ROTATION*(pointerType==='touch'?.75:1));
    assert.equal(controls.zoomSpeed,zoom);assert.equal(controls.panSpeed,pan);assert(controls.enableZoom&&controls.enablePan);
    if(pointerType==='mouse')controls._handleMouseMoveRotate({clientX:100,clientY:0});
    else{controls._pointers=[1];controls._handleTouchMoveRotate({pageX:100,pageY:0});}
    for(let i=0;i<400;i++)controls.update();
    assert(Math.abs(controls.getAzimuthalAngle()+Math.PI/4*controls.rotateSpeed)<1e-7);
    input.set(.1);assert.equal(controls.rotateSpeed,.1*(pointerType==='touch'?.75:1));
    input.set(NaN);assert.equal(controls.rotateSpeed,DEFAULT_ROTATION*(pointerType==='touch'?.75:1));input.dispose();
  }
  const html=await fs.readFile(new URL('./index.html',import.meta.url),'utf8');
  assert.equal([...html.matchAll(/id="fullscreen"/g)].length,1);
  assert(/<footer[\s\S]*id="fullscreen"[\s\S]*<\/footer>/.test(html));
});
