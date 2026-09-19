import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {SHOTS,smoothProgress,fadeAt,advanceShot} from './camera-paths.js';
import * as Three from '../3d/vendor/three.module.js';
import {LectureClock,boardSlot,boardHeights} from './lecture-state.js';
import {configureCameraInput,DEFAULT_ROTATION} from './camera-input.js';

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
  for(const file of ['index.html','app.js','scene.js','camera-paths.js','lecture.js','lecture-state.js']){
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
  for(const match of app.matchAll(/\$\('([^']+)'\)/g))assert(ids.has(match[1]),'Missing element '+match[1]);
});

test('scene assembly creates valid model buffers without a browser or GPU',async()=>{
  const coreURL=new URL('../3d/vendor/three.module.js',import.meta.url).href;
  const asModule=source=>'data:text/javascript;base64,'+Buffer.from(source).toString('base64');
  async function inlineAddon(file){return asModule((await fs.readFile(new URL(file,import.meta.url),'utf8')).replaceAll("from 'three'",`from '${coreURL}'`));}
  let source=await fs.readFile(new URL('./scene.js',import.meta.url),'utf8');
  source=source.replace("import * as THREE from 'three';",'const THREE=globalThis.__retreatTestThree;');
  for(const file of ['./vendor/geometries/RoundedBoxGeometry.js','./vendor/objects/Water.js','./vendor/objects/Sky.js'])source=source.replace(file,await inlineAddon(file));
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
    assert(instances>10000);assert(triangles<5000000);
    assert(calls.includes('NS 方程 · 存在性与光滑性'));assert(calls.includes('Hodge 猜想 ？'));assert(calls.includes('数学难民营'));
    assert(calls.includes('NS'));assert.equal(clippedFragments,12);
    for(const name of ['NS conjecture blackboard','Hodge conjecture blackboard','Entrance lintel sign','Entrance wayfinding sign'])assert(scene.getObjectByName(name)?.isMesh,name);
    assert(!calls.some(text=>text.includes('已解决')));
    assert(result.water.material.uniforms.time);assert.equal(typeof result.lighting,'function');
    result.lighting(0,true);result.lighting(100,true);result.dispose();
    assert.deepEqual(result.ocean.material.uniforms.sunDirection.value.toArray(),result.water.material.uniforms.sunDirection.value.toArray());
    console.log(JSON.stringify({sceneObjects:scene.children.length,instances,triangles}));
  }finally{delete globalThis.__retreatTestThree;delete globalThis.document;}
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
    lecture.lift(0,1);for(let i=0;i<50;i++)lecture.update(.1);
    assert(Math.abs(boards[0].position.y-3.7)<.001);assert(Math.abs(boards[1].position.y-1.45)<.001);
    lecture.select(64);await Promise.resolve();lecture.staticPage();lecture.update(.1,true);
    assert.equal(lecture.clock.page,64);assert.equal(lecture.clock.slots[lecture.clock.active].progress,1);
    assert(!scene.getObjectByName('Writing chalk').visible);assert(!scene.getObjectByName('Moving blackboard eraser').visible);
    for(const board of boards)assert(board.position.toArray().every(Number.isFinite));
    assert(lecture.focus().toArray().every(Number.isFinite));lecture.dispose();
  }finally{globalThis.fetch=originalFetch;globalThis.Image=originalImage;globalThis.document=originalDocument;}
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
