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
import {bindCameraIntent} from './camera-intent.js';
import {BUILDING_SCALE,riverPoint,watercourse,LAWNS,GIANT_TREES,BAMBOO_GROVES,POOL_RECTS,poolTopology,inPool,inBuilding,BRIDGES,bridgeHeight,HALL,DECK_Y,POOL_LEVEL,POOL_DEPTH,configureLectureRoot,lectureViewOffset,LECTURE_SCALE} from './site-layout.js?v=9-peninsula';
import {writingPose,rowReveal,eraserPose,wetOpacity,chalkLength,inkGuides,ERASER_HALF_WIDTH,ERASER_HALF_HEIGHT} from './chalk-motion.js?v=7-garden';

test('pool is one connected nonoverlapping union with an open core and sunrise edge',()=>{
  const {cells,edges}=poolTopology();
  assert(cells.length>10);assert(edges.length>10);
  const area=cells.reduce((sum,[a,b,c,d])=>sum+(b-a)*(d-c),0);
  assert.equal(area,952); // Ring 576 + core 96 + arms 192 + east edge 88.
  for(let i=0;i<cells.length;i++)for(let j=i+1;j<cells.length;j++){
    const [a,b,c,d]=cells[i],[e,f,g,h]=cells[j];
    assert(Math.min(b,f)<=Math.max(a,e)||Math.min(d,h)<=Math.max(c,g),'Reflection triangles cannot overlap');
  }
  const visited=new Set([0]),queue=[0];
  while(queue.length){
    const [a,b,c,d]=cells[queue.shift()];
    cells.forEach(([e,f,g,h],j)=>{
      const adjacent=((Math.abs(b-e)<1e-8||Math.abs(f-a)<1e-8)&&Math.min(d,h)>Math.max(c,g))||((Math.abs(d-g)<1e-8||Math.abs(h-c)<1e-8)&&Math.min(b,f)>Math.max(a,e));
      if(adjacent&&!visited.has(j)){visited.add(j);queue.push(j);}
    });
  }
  assert.equal(visited.size,cells.length);
  for(const [a,b,c,d] of cells){
    const x=(a+b)/2,z=(c+d)/2;assert(inPool(x,z));assert(!inBuilding(x,z));
    assert(elevation(x,z)<POOL_LEVEL-POOL_DEPTH-.1,'Basin must clear terrain');
  }
  assert(inPool(3.5,0),'Pool passes through the core court');
  assert(!inPool(-6,-4));assert(!inPool(11.5,-4));assert(inPool(48,0));
  assert.equal(Math.max(...POOL_RECTS.map(r=>r[1])),50);
});

test('arched bridges land on dry banks and offer level companion crossings',()=>{
  assert.equal(BRIDGES.length,3);
  for(const b of BRIDGES){
    assert(inPool(b.x,b.z));assert(!inPool(b.x-b.span/2,b.z));assert(!inPool(b.x+b.span/2,b.z));
    assert.equal(bridgeHeight(b,0),DECK_Y);assert(Math.abs(bridgeHeight(b,1)-DECK_Y)<1e-10);
    for(let i=0;i<=100;i++){const h=bridgeHeight(b,i/100);assert(h>=DECK_Y&&h<=DECK_Y+b.rise+1e-10);}
  }
});

test('compact east-facing boards fit the hall and camera follows their west-facing normals',()=>{
  const root=new Three.Group();configureLectureRoot(root);root.updateMatrixWorld(true);
  const forward=new Three.Vector3(0,0,1).applyQuaternion(root.quaternion);
  assert(forward.distanceTo(new Three.Vector3(-1,0,0))<1e-12);
  const floor=DECK_Y*BUILDING_SCALE,ceiling=floor+HALL.clearHeight;
  for(const u of [22.4,28,33.6])for(const lift of [0,.25,.5,.75,1])for(const v of boardHeights(lift)){
    const center=root.localToWorld(new Three.Vector3(u,v,-10.4));
    assert(Math.abs(center.x-HALL.boardX*BUILDING_SCALE)<1e-8);
    assert(center.y-1.025*LECTURE_SCALE>floor);
    assert(center.y+1.025*LECTURE_SCALE<ceiling);
    assert(Math.abs(center.z)+2.65*LECTURE_SCALE<HALL.south*BUILDING_SCALE);
  }
  const offset=new Three.Vector3(...lectureViewOffset(5));
  assert(offset.x<0&&offset.y===0&&offset.z===0);
  const shot=SHOTS.find(s=>s.name==='报告厅');
  for(const p of shot.positions){assert(p[0]>HALL.west*BUILDING_SCALE&&p[0]<HALL.boardX*BUILDING_SCALE);assert(Math.abs(p[2])<.01);assert(p[1]<ceiling);}
});

test('offshore room and sunrise edge sit over sea while arrival stays west-connected',()=>{
  for(const x of [HALL.west,(HALL.west+HALL.east)/2,HALL.east,50]){
    for(const z of [HALL.north,0,HALL.south])assert(elevation(x,z)<seaLevel);
  }
  for(const x of [-70,-50,-24,-19])assert(elevation(x,8)>seaLevel);
  for(let x=51;x<450;x+=9)for(let z=-150;z<=150;z+=15)assert(elevation(x,z)<seaLevel);
});


test('eight finite camera chapters with auditorium, ocean and garden views',()=>{
  assert.equal(SHOTS.length,8);assert(SHOTS.some(s=>s.lecture));assert(SHOTS.some(s=>s.name==='海景露台'));assert(SHOTS.some(s=>s.name==='山水花园'));
  for(const shot of SHOTS){
    assert(shot.duration>=20);assert(shot.fov>30&&shot.fov<70);
    for(const points of [shot.positions,shot.targets]){
      const curve=new Three.CatmullRomCurve3(points.map(p=>new Three.Vector3(...p)));
      for(let i=0;i<=100;i++)assert(curve.getPointAt(smoothProgress(i/100)).toArray().every(Number.isFinite));
    }
  }
  assert.equal(fadeAt(0),1);assert.equal(fadeAt(.5),0);assert(Math.abs(fadeAt(1)-1)<1e-9);
  const wrap=advanceShot(7,37.98,.05,1);assert.equal(wrap.index,0);assert(wrap.time>=0&&wrap.time<.1);
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
  const modules=new Map();
  async function inlineAddon(file){
    const url=new URL(file,import.meta.url);
    if(modules.has(url.href))return modules.get(url.href);
    let code=await fs.readFile(url,'utf8');
    code=code.replace("import * as THREE from 'three';",'const THREE=globalThis.__retreatTestThree;').replaceAll("from 'three'",`from '${coreURL}'`);
    const dependencies=[...code.matchAll(/from\s+['"](\.[^'"]+)['"]/g)];
    for(const match of dependencies)code=code.replace(match[1],await inlineAddon(new URL(match[1],url).href));
    const result=asModule(code);modules.set(url.href,result);return result;
  }
  const sceneModule=await inlineAddon('./scene.js');
  const calls=[];let clippedFragments=0;
  globalThis.__retreatTestThree={...Three,
    TextureLoader:class{async loadAsync(){const texture=new Three.Texture();texture.image={width:256,height:256};return texture;}},
    PMREMGenerator:class{fromScene(){return {texture:new Three.Texture(),dispose(){}};}dispose(){}}
  };
  globalThis.document={createElement:()=>({width:0,height:0,getContext:()=>({fillRect(){},fillText(text){calls.push(text);},save(){},restore(){},translate(){},rotate(){},beginPath(){},moveTo(){},lineTo(){},closePath(){},clip(){clippedFragments++;},drawImage(){}})})};
  try{
    const {createRetreat}=await import(sceneModule);
    const scene=new Three.Scene();
    const result=await createRetreat({capabilities:{getMaxAnisotropy:()=>8}},scene,()=>{});
    assert(result.water.isMesh);assert(result.ocean.isMesh);assert(result.sculpture.isMesh);assert(scene.environment);
    assert(!scene.getObjectByName('Ocean conference table'));
    const auditorium=scene.getObjectByName('Mathematics auditorium seating');assert.equal(auditorium.userData.seats,32);assert.deepEqual(auditorium.userData.facing,[1,0,0]);
    assert(scene.getObjectByName('Small seminar lectern'));assert.equal(auditorium.userData.architectureScale,BUILDING_SCALE);
    assert(Math.abs(BUILDING_SCALE**2-2)<1e-12);
    assert(auditorium.userData.seatPositions.every(p=>p[0]>HALL.west&&p[0]<HALL.boardX&&Math.abs(p[2])>=.75));
    assert.equal(auditorium.userData.clearHeight,3.2);assert(auditorium.userData.offshore);
    assert.equal(scene.children.filter(o=>o.name.startsWith('Small arch bridge ')).length,3);
    assert.equal(scene.children.filter(o=>o.name.startsWith('Level pool crossing ')).length,3);
    assert.equal(scene.getObjectByName('Low sea-facing seminar hall').userData.clearHeight,3.2);
    assert(scene.getObjectByName('Connected infinity pool and core water court'));assert(scene.getObjectByName('East infinity overflow sheet'));
    assert(scene.getObjectByName('Independent quiet library'));assert(scene.getObjectByName('Quiet residential villa 1'));assert(scene.getObjectByName('Quiet residential villa 2'));
    result.campus.setTeachingShade(true);assert(scene.getObjectByName('East teaching blackout shade').visible);result.campus.setTeachingShade(false);
    assert(scene.getObjectByName('Conference entrance sign').isMesh);
    assert.equal(result.ocean.position.y,result.site.seaLevel);
    // Floor slabs must never cover swimming lanes, except the explicit level
    // crossing beside each arch. This catches a visually hidden water court.
    for(const f of result.layoutFloors.filter(f=>f.y===0))for(const [a,b,c,d] of poolTopology().cells){
      const left=Math.max(a,f.cx-f.w/2),right=Math.min(b,f.cx+f.w/2),near=Math.max(c,f.cz-f.d/2),far=Math.min(d,f.cz+f.d/2);
      if(right-left<.0001||far-near<.0001)continue;
      assert(BRIDGES.some(br=>Math.abs(f.cx-br.x)<.001&&Math.abs(f.cz-(br.z+br.width/2+1))<.001),'Unexpected floor slab covers the pool: '+JSON.stringify(f));
    }
    for(const z of [-14,0,14]){
      assert(result.site.elevation(0,z)>result.site.seaLevel);
      assert(result.site.elevation(HALL.west*BUILDING_SCALE,z)<result.site.seaLevel);
      assert(result.site.elevation(result.site.coastline(z)+15,z)<result.site.seaLevel);
    }
    let instances=0,triangles=0;
    for(const object of scene.children){
      if(!object.geometry)continue;
      assert([...object.geometry.attributes.position.array].every(Number.isFinite));
      if(object.isInstancedMesh){assert([...object.instanceMatrix.array].every(Number.isFinite));instances+=object.count;}
      if(object.isMesh)triangles+=(object.geometry.index?.count || object.geometry.attributes.position.count)/3*(object.isInstancedMesh?object.count:1);
    }
    console.log(JSON.stringify({sceneObjects:scene.children.length,instances,triangles,forestTrees:result.landscape.plantings.length}));
    assert(instances>1500);assert(triangles<1300000,`Expanded garden and auditorium must stay within the 1.3M scene budget: ${triangles}`);
    assert(scene.children.filter(o=>o.isMesh).length<330,'Spatial instancing must bound model draw batches');
    for(const name of ['Continuous mountain ridges','Detailed coastal terrain','Olive leaf canopies','Palm fronds','Fern understory','Coastal grasses','Weathered coastal outcrops'])assert(scene.getObjectByName(name),name);
    for(const name of ['Giant tree crowns','Jointed bamboo stems','Bamboo leaf sprays','Soft lawn garden','Garden flower borders','Connected waterfall and winding creek'])assert(scene.getObjectByName(name),name);
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
  for(const [x,z] of [[0,0],[-37,-16],[-56,-28],[-15,12]])assert.equal(elevation(x,z),-1.1);
  for(let z=-600;z<=600;z+=5){
    assert(Math.abs(elevation(shoreline(z),z)-seaLevel)<.0001);
    assert(shoreline(z)>coastline(z)-2&&shoreline(z)<coastline(z)+7);
    assert(!canPlant(coastline(z)+15,z));
  }
  for(let x=-500;x<100;x+=8)for(let z=-500;z<200;z+=8){assert(Number.isFinite(elevation(x,z)));assert(Number.isFinite(slope(x,z)));assert(Math.abs(elevation(x+.001,z)-elevation(x,z))<.1);}
  assert(elevation(-260,0)>60);assert(!canPlant(HALL.west,0));
  for(const x of [0,20,35,100,300])for(const z of [-160,-100,100,160])assert(elevation(x,z)<seaLevel,'North and south must remain open sea');
  for(const z of [-60,0,60])assert(elevation(100,z)<seaLevel,'Eastern horizon has no land');
});

test('water descends through the garden, is carved below the surface and avoids the buildings',()=>{
  let previous=Infinity;
  for(let i=0;i<=300;i++){
    const p=riverPoint(i/300);assert(p.y<=previous+1e-8);previous=p.y;
    assert(!inPool(p.x,p.z,1));assert(!inBuilding(p.x,p.z));
    assert(elevation(p.x,p.z)<p.y-.3,'Water surface must not be buried in the terrain');
    assert(watercourse(p.x,p.z).distance<.05);
  }
  assert.equal(LAWNS.length,2);assert.equal(GIANT_TREES.length,3);assert.equal(BAMBOO_GROVES.length,3);
});

test('chalk lift, wear, damp wiping and drying are bounded and deterministic',()=>{
  const rows=[[80,40,500,70],[100,180,800,100]];
  assert(!writingPose(rows,0).contact);assert.equal(rowReveal(1,1,2),1);
  for(let i=0;i<=100;i++){const p=writingPose(rows,i/100),e=eraserPose(i/100);assert([p.x,p.y,e.x,e.y,e.angle].every(Number.isFinite));assert(e.angle<-.1);}
  assert(chalkLength(.07)<chalkLength(0));assert.equal(chalkLength(10),.045);
  assert(wetOpacity(0)>wetOpacity(6));assert.equal(wetOpacity(12),0);
  const data=new Uint8ClampedArray(20*20*4);for(let x=1;x<10;x++)data[(8*20+x)*4+3]=255;
  const guides=inkGuides({data,width:20,height:20},[[0,0,19,19]]);assert(guides[0].includes(8));assert(guides[0].includes(null));
  const wipes=Array.from({length:701},(_,i)=>eraserPose(i/700)).filter(p=>p.contact);
  for(let y=0;y<=640;y+=20)for(let x=0;x<=1536;x+=24){
    assert(wipes.some(p=>{const dx=x-p.x,dy=y-p.y,c=Math.cos(p.angle),s=Math.sin(p.angle);return Math.abs(dx*c+dy*s)<=ERASER_HALF_WIDTH&&Math.abs(-dx*s+dy*c)<=ERASER_HALF_HEIGHT;}),'Tilted wipe must cover the whole board');
  }
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
  source=source.replace("from 'three'",`from '${core}'`).replace('./lecture-state.js?v=7-garden',state).replace('./chalk-motion.js?v=7-garden',new URL('./chalk-motion.js',import.meta.url).href);
  const originalFetch=globalThis.fetch,originalImage=globalThis.Image,originalDocument=globalThis.document;
  const contexts=[];
  globalThis.document={createElement:()=>({width:0,height:0,getContext(){
    const ctx={drawImage(){},fillRect(){},save(){},restore(){},beginPath(){},rect(){},clip(){},translate(){},rotate(){}};contexts.push(ctx);return ctx;
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
    assert(scene.getObjectByName('Writing chalk').userData.length<.17);
    assert(scene.getObjectByName('Falling chalk powder').geometry.attributes.position.count===64);
    lecture.playing=false;const time=lecture.clock.elapsed;lecture.update(.1);assert.equal(lecture.clock.elapsed,time);
    const uploads=boards.map(b=>b.children[0].material.map.version);
    for(let i=0;i<50;i++)lecture.update(.1);
    assert.deepEqual(boards.map(b=>b.children[0].material.map.version),uploads,'Unchanged boards must not re-upload textures');
    lecture.lift(0,1);for(let i=0;i<50;i++)lecture.update(.1);
    assert(Math.abs(boards[0].position.y-3.7)<.001);assert(Math.abs(boards[1].position.y-1.45)<.001);
    lecture.select(64);await Promise.resolve();lecture.staticPage();lecture.update(.1,true);
    assert.equal(lecture.clock.page,64);assert.equal(lecture.clock.slots[lecture.clock.active].progress,1);
    assert(!scene.getObjectByName('Writing chalk').visible);assert(!scene.getObjectByName('Moving blackboard eraser').visible);
    assert(!scene.getObjectByName('Falling chalk powder').visible);
    assert(boards.every(b=>b.children[0].material.roughnessMap.isCanvasTexture));
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

test('drag-release clicks never restart touring; fresh clicks and keyboard remain usable',async()=>{
  const handlers=new Map(),windowHandlers=new Map();let now=0,touring=true,manualCount=0;
  const canvas={contains:()=>false},button={closest:()=>true},slider={closest:()=>null};
  const root={hidden:false,addEventListener(type,fn){handlers.set(type,fn);},removeEventListener(type){handlers.delete(type);},defaultView:{addEventListener(type,fn){windowHandlers.set(type,fn);},removeEventListener(type){windowHandlers.delete(type);}}};
  const guard=bindCameraIntent(root,canvas,()=>{touring=false;manualCount++;},()=>now);
  function emit(type,extra={}){const event={pointerId:1,pointerType:'mouse',clientX:10,clientY:10,target:canvas,preventDefault(){this.prevented=true;},stopImmediatePropagation(){this.stopped=true;},...extra};handlers.get(type)?.(event);return event;}
  for(const pointerType of ['mouse','touch','pen']){
    touring=true;emit('pointerdown',{pointerType});assert(!touring);assert(!guard.canActivate());
    emit('pointermove',{clientX:100,pointerType});emit('pointerup',{clientX:100,pointerType});
    const click=emit('click',{target:button});assert(click.prevented&&click.stopped);assert(!guard.canActivate());assert(!touring);
    now+=1000;assert(guard.canActivate());assert(!touring,'Idle time must never resume the tour');
  }
  // A deliberate new button press is usable immediately after the drag,
  // without relying on a guessed long lockout timer.
  emit('pointerdown');emit('pointerup',{clientX:100});assert(!guard.canActivate());
  emit('pointerdown',{target:button});emit('pointerup',{target:button});assert(!emit('click',{target:button}).stopped);assert(guard.canActivate());
  assert(!emit('click',{target:button,detail:0}).stopped,'Keyboard activation is supported');
  const prior=manualCount;emit('pointerdown',{target:slider});emit('pointermove',{target:slider,clientX:99});emit('pointerup',{target:slider,clientX:99});assert.equal(manualCount,prior,'Changing lighting/sensitivity is not a camera drag');
  emit('pointerdown',{pointerType:'touch',pointerId:1});emit('pointerdown',{pointerType:'touch',pointerId:2});
  emit('pointerup',{pointerId:1});assert(!guard.canActivate());emit('pointercancel',{pointerId:2});assert(!guard.canActivate());
  now+=1000;emit('pointerdown');windowHandlers.get('blur')();assert(!guard.hasPointers());now+=1000;assert(guard.canActivate());
  guard.dispose();assert.equal(handlers.size,0);assert.equal(windowHandlers.size,0);
  const app=await fs.readFile(new URL('./app.js',import.meta.url),'utf8');
  assert.equal([...app.matchAll(/resumeTour\(\)/g)].length,2,'Only the definition and explicit tour-button handler may start touring');
  assert(app.includes('controls.autoRotate=false'));
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
