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
import {BUILDING_SCALE,riverPoint,watercourse,LAWNS,GIANT_TREES,BAMBOO_GROVES,POOL_RECTS,poolTopology,inPool,inBuilding,BRIDGES,COURT_DECKS,COFFEE_PAD,SEA_TERRACE,SEA_STEPS,DISTANT_ISLANDS,HALL,DECK_Y,configureLectureRoot,lectureViewOffset,LECTURE_SCALE,ROOM_PADS,GARDEN_PADS,ORNAMENTAL_TREES} from './site-layout.js?v=18-board-diagrams';
import {writingPlan,erasingPlan,writingPose,inkReveal,rowReveal,eraserPose,wetOpacity,chalkLength,inkGuides,ERASER_HALF_WIDTH,ERASER_HALF_HEIGHT} from './chalk-motion.js?v=18-board-diagrams';
import {chalkCopy,composeChalkPage} from './chalk-language.js';
import {RetreatTime,daylightAt} from './retreat-time.js';
import {constrainAboveWater} from './camera-bounds.js';
import {bindPhysicalButtons} from './physical-buttons.js';
import {platformUnion} from './platform-union.js';
test('overlapping platform paths become a single surface without depth-fighting',()=>{
  const {cells,edges}=platformUnion([[0,4,0,2],[1,3,-1,3],[0,4,0,2]]);
  assert.equal(cells.reduce((sum,[a,b,c,d])=>sum+(b-a)*(d-c),0),12);
  assert(edges.length>4);
  for(const [a,b,c,d] of cells)assert(a<b&&c<d);
});

test('physical buttons click once, cancel drags, and restore camera controls',()=>{
  const events={},canvas={addEventListener(t,f){events[t]=f;},removeEventListener(t){delete events[t];},setPointerCapture(){},releasePointerCapture(){}};
  const controls={enabled:true},object={userData:{action:'roof'}},actions=[];
  const binding=bindPhysicalButtons(canvas,controls,()=>object,a=>actions.push(a));
  const event=(x=0,id=1)=>({button:0,pointerId:id,clientX:x,clientY:0,preventDefault(){},stopImmediatePropagation(){}});
  events.pointerdown(event());assert(!controls.enabled);assert(object.userData.pressed);
  events.pointerup(event(2));assert(controls.enabled);assert(!object.userData.pressed);assert.deepEqual(actions,['roof']);
  events.pointerdown(event());events.pointerup(event(20));assert.equal(actions.length,1);assert(controls.enabled);
  events.pointerdown(event());events.pointercancel(event());assert(controls.enabled);assert.equal(actions.length,1);
  controls.enabled=false;events.pointerdown(event());events.lostpointercapture(event());assert(!controls.enabled);
  binding.dispose();assert.deepEqual(events,{});
});

test('chalk skips blank trailing columns and lifts across inter-word gaps',()=>{
  const rows=[[0,0,200,20]],data=new Uint8ClampedArray(220*20*4);
  for(const x of [10,15,20,55,60])data[(8*220+x)*4+3]=255;
  const guide=inkGuides({data,width:220,height:20},rows);
  for(let i=9;i<=100;i++){
    const p=writingPose(rows,i/100,guide);assert(p.x<=60.0001,'No sweep to the empty right edge');
    if(p.x>21&&p.x<54)assert(!p.contact,'Pen must lift across whitespace');
    if(!p.entering)assert(inkReveal(rows,i/100,0,guide)>=p.x||i===100);
  }
  assert.equal(writingPose(rows,1,guide).x,60);
  const blank=inkGuides({data:new Uint8ClampedArray(220*20*4),width:220,height:20},rows);
  assert(!writingPose(rows,.8,blank).contact);
});

test('all consolidated handwritten captions switch languages without changing formulas',async()=>{
  const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/pages.json',import.meta.url),'utf8'));
  const ctx={clearRect(){},fillText(){},drawImage(){},measureText(t){return {width:[...t].length*25};}};
  for(const [i,p] of pages.entries())for(const lang of ['zh','en']){
    const copy=chalkCopy(p,lang);assert(copy.title&&copy.text);
    if(lang==='en')assert(!/[\u3400-\u9fff]/.test(copy.title+copy.text+copy.source));
    const rows=composeChalkPage(ctx,p,i,lang,{});
    for(const [x,y,w,h] of rows){assert(x>=0&&y>=0&&x+w<=1536&&y+h<=604);}
  }
  const css=await fs.readFile(new URL('./board-console.css',import.meta.url),'utf8');
  for(const match of css.matchAll(/url\('([^']+)'\)/g))assert((await fs.stat(new URL(match[1],import.meta.url))).size>1000);
});

test('clock follows local wall time across midnight, resume and reduced motion; preview is explicit',()=>{
  let now=new Date(2026,8,22,23,59,50);const clock=new RetreatTime(()=>now);
  assert(Math.abs(clock.hour-(23+59/60+50/3600))<1e-9);
  now=new Date(2026,8,23,0,0,5);clock.update(999,true);assert(Math.abs(clock.hour-5/3600)<1e-9);
  clock.previewAt(21);now=new Date(2026,8,23,9,25,0);clock.update(1000);assert.equal(clock.hour,21);
  assert(clock.preview);clock.sync();assert(!clock.preview);assert.equal(clock.hour,9+25/60);
  now=new Date(2026,8,23,17,45,0);clock.update(0);assert.equal(clock.hour,17.75);
  assert.equal(daylightAt(0),0);assert.equal(daylightAt(12),1);
});

test('compact sea terraces connect across seawater with three arch bridges',()=>{
  assert.deepEqual(POOL_RECTS,[]);assert.deepEqual(poolTopology(),{cells:[],edges:[]});
  assert.equal(BRIDGES.length,3);assert.equal(COURT_DECKS.length,2);
  assert(SEA_TERRACE[1]===56&&SEA_TERRACE[1]>HALL.east);
  const pads=[...COURT_DECKS,SEA_TERRACE,COFFEE_PAD];
  const dry=(x,z)=>pads.some(([a,b,c,d])=>x>a&&x<b&&z>c&&z<d);
  for(const b of BRIDGES){
    assert(!dry(b.x,b.z),'Bridge center is above seawater');
    for(const sign of [-1,1])assert(dry(b.x+(b.axis==='x'?sign*b.span/2:0),b.z+(b.axis==='z'?sign*b.span/2:0)),'Bridge ends overlap dry decks');
    assert(b.rise>0&&b.rise<.5);
  }
  assert((DECK_Y-seaLevel)*BUILDING_SCALE>1.3);
});

test('distant islands keep the sunrise corridor clear',()=>{
  assert.equal(DISTANT_ISLANDS.length,4);
  for(const island of DISTANT_ISLANDS){
    assert(Math.hypot(island.x-SEA_TERRACE[1],island.z)-Math.max(island.rx,island.rz)*1.15>170);
    if(island.x>SEA_TERRACE[1])assert(Math.abs(island.z)-island.rz*1.15>(island.x+island.rx*1.15-SEA_TERRACE[1])*Math.tan(Math.PI/8));
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
    assert(center.y-1.025*LECTURE_SCALE>=floor+1.35);
    assert(center.y+1.025*LECTURE_SCALE<ceiling);
    assert(Math.abs(center.z)+2.65*LECTURE_SCALE<HALL.south*BUILDING_SCALE);
  }
  const offset=new Three.Vector3(...lectureViewOffset(5));
  const backingTop=root.localToWorld(new Three.Vector3(28,5.05,-10.82));
  assert(backingTop.y<ceiling-.2,'The complete backing, not just the writing panels, clears the roof');
  assert(offset.x<0&&offset.y===0&&offset.z===0);
  const shot=SHOTS.find(s=>s.name==='报告厅');
  for(const p of shot.positions){assert(p[0]>HALL.west*BUILDING_SCALE&&p[0]<HALL.boardX*BUILDING_SCALE);assert(Math.abs(p[2])<.01);assert(p[1]<ceiling);}
});

test('all facility footprints and expansion docks sit over open seawater',()=>{
  for(const x of [HALL.west,(HALL.west+HALL.east)/2,HALL.east,50]){
    for(const z of [HALL.north,0,HALL.south])assert(elevation(x,z)<seaLevel);
  }
  for(const x of [-70,-50,-24,-19])assert(elevation(x,8)<seaLevel);
  for(const [a,b,c,d] of [...ROOM_PADS,...GARDEN_PADS])for(const x of [a,(a+b)/2,b])for(const z of [c,(c+d)/2,d])assert(elevation(x,z)<seaLevel);
  for(let x=51;x<450;x+=9)for(let z=-150;z<=150;z+=15)assert(elevation(x,z)<seaLevel);
});


test('eight finite camera chapters with auditorium, ocean and garden views',()=>{
  assert.equal(SHOTS.length,8);assert(SHOTS.some(s=>s.lecture));assert(SHOTS.some(s=>s.name==='海景露台'));assert(SHOTS.some(s=>s.name==='海上花园'));
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
    assert(!result.water);assert(result.ocean.isMesh);assert(result.sculpture.isMesh);assert(scene.environment);
    assert(!scene.getObjectByName('Ocean conference table'));
    const auditorium=scene.getObjectByName('Mathematics auditorium seating');assert.equal(auditorium.userData.seats,30);assert.deepEqual(auditorium.userData.facing,[1,0,0]);
    assert.equal(auditorium.userData.seatsPerRow,10);
    assert(Math.abs(LECTURE_SCALE/.6-1.2)<1e-10);
    const frontX=Math.max(...auditorium.userData.seatPositions.map(p=>p[0]));
    assert((HALL.boardX-frontX)*BUILDING_SCALE>4.9,'First row must be set back from the boards');
    for(const x of new Set(auditorium.userData.seatPositions.map(p=>p[0])))assert.equal(auditorium.userData.seatPositions.filter(p=>p[0]===x).length,10);
    assert.equal(auditorium.userData.rows,3);assert.equal(HALL.south-HALL.north,20);
    assert.deepEqual(auditorium.userData.rowRises,[.36,.18,0]);
    const seatLevels=[...new Set(auditorium.userData.seatPositions.map(p=>p[1]))];assert.equal(seatLevels.length,3);
    assert(Math.abs((seatLevels[0]-seatLevels[1])*BUILDING_SCALE-.18)<1e-10);
    assert(scene.getObjectByName('Warm woven seminar carpet').material.roughness===1);
    const frontCarpet=scene.getObjectByName('Warm woven seminar carpet').material.color;
    const middleCarpet=scene.getObjectByName('Carpeted seating tier 1 1').material.color;
    const rearCarpet=scene.getObjectByName('Carpeted seating tier 0 1').material.color;
    for(const c of ['r','g','b'])assert(frontCarpet[c]>middleCarpet[c]&&middleCarpet[c]>rearCarpet[c]);
    assert.equal(scene.getObjectByName('Central carpeted stair aisle').userData.stepHeightMetres,.09);
    assert.equal(scene.getObjectByName('Transparent seminar side elevations').userData.northOpaqueWall,false);
    const paving=scene.getObjectByName('Honed limestone terrace paving').userData;
    assert(paving.largeFormat&&paving.slabs>100);assert(paving.jointMetres<.007);assert.equal(paving.roughness,.96);
    assert(scene.getObjectByName('Small seminar lectern'));assert.equal(auditorium.userData.architectureScale,BUILDING_SCALE);
    assert(Math.abs(BUILDING_SCALE**2-2)<1e-12);
    assert(auditorium.userData.seatPositions.every(p=>p[0]>HALL.west&&p[0]<HALL.boardX&&Math.abs(p[2])>=.75));
    assert.equal(auditorium.userData.clearHeight,4.9);assert(auditorium.userData.offshore);
    assert.equal(scene.children.filter(o=>o.name.startsWith('Small arch bridge ')).length,0);
    assert.equal(scene.children.filter(o=>o.name.startsWith('Level pool crossing ')).length,0);
    assert.equal(scene.getObjectByName('Low sea-facing seminar hall').userData.clearHeight,4.9);
    assert.equal(result.campus.lightingZones.filter(z=>z.task==='blackboard').length,3);
    for(const name of ['Upper private studies','Upper small seminar','Upper seminar lounge'])assert(result.campus.lightingZones.some(z=>z.name===name));
    assert.equal(result.pathLighting.count,26);const lanterns=scene.children.filter(o=>o.name.startsWith('Platform path lantern '));assert.equal(new Set(lanterns.map(o=>o.userData.type)).size,3);
    const spots=scene.children.filter(o=>o.isSpotLight);
    result.setTime(12);const daytime=spots.map(o=>o.intensity);result.setTime(23);assert.equal(result.ocean.material.uniforms.nightVisibility.value,.06);
    spots.forEach((lamp,i)=>{assert(lamp.intensity>daytime[i]);assert(lamp.distance>0&&lamp.intensity>60);});
    for(const name of ['Academic living villa','Discussion villa','Upper private studies','Upper small seminar','Independent quiet library','Quiet residential villa 1','Quiet residential villa 2','Service and tea kitchen','Seminar hall','Bamboo tea pavilion'])assert(scene.getObjectByName(name+' light fixtures'));
    for(const lamp of scene.children.filter(o=>o.isSpotLight)){assert(lamp.position.y>lamp.target.position.y);assert.equal(lamp.penumbra,.85);assert(!lamp.castShadow);}
    const fills=scene.children.filter(o=>o.isPointLight);assert.equal(fills.length,4);
    for(const lamp of fills){assert(!lamp.castShadow);assert.equal(lamp.userData.task,'seminar-fill');assert(lamp.position.x>HALL.west*BUILDING_SCALE&&lamp.position.x<HALL.east*BUILDING_SCALE);assert(lamp.intensity>0&&lamp.distance<16);}
    for(const name of ['Connected infinity pool and core water court','East infinity overflow sheet','Side infinity overflow sheet','Sunrise infinity edge'])assert(!scene.getObjectByName(name));
    assert.equal(result.islands.group.children.length,4);assert.equal(result.sculptures.length,10);
    for(const island of result.islands.group.children){
      const pos=island.geometry.attributes.position;
      for(let i=1;i<=96;i++)assert.equal(pos.getY(i),pos.getY(0),'Island pole must not split into vertical spikes');
      assert([...island.geometry.attributes.normal.array].every(Number.isFinite));
    }
    for(const sculpture of result.sculptures){
      assert(result.layoutFloors.some(f=>f.y===0&&Math.abs(sculpture.position.x/BUILDING_SCALE-f.cx)+1.3<=f.w/2+.001&&Math.abs(sculpture.position.z/BUILDING_SCALE-f.cz)+1.3<=f.d/2+.001),'Each sculpture needs a complete dry pedestal pad: '+sculpture.name);
    }
    assert.equal(new Set(result.sculptures.map(o=>o.userData.facility)).size,10);
    const stairs=scene.children.filter(o=>o.name.startsWith('Sea access stair '));assert.equal(stairs.length,SEA_STEPS.length);
    for(const stair of stairs){const d=stair.userData;assert.equal(d.steps,7);assert(d.riserMetres>.15&&d.riserMetres<.2);assert(d.treadMetres>.5);assert(Math.abs(d.heights.at(-1)-seaLevel-.025)<1e-8);for(let i=1;i<d.heights.length;i++)assert(d.heights[i]<d.heights[i-1]);}
    assert(scene.getObjectByName('Independent quiet library'));assert(scene.getObjectByName('Quiet residential villa 1'));assert(scene.getObjectByName('Quiet residential villa 2'));
    result.campus.setTeachingShade(true);assert(scene.getObjectByName('East teaching blackout shade').visible);result.campus.setTeachingShade(false);
    assert(scene.getObjectByName('Conference entrance sign').isMesh);
    assert.equal(result.ocean.position.y,result.site.seaLevel);
    // Retained terraces and the coffee pavilion have dry foundations.
    for(const [x,z] of [[0,0],[10,2],[52,0],[39,-22]]){
      assert(result.layoutFloors.some(f=>f.y===0&&Math.abs(x-f.cx)<f.w/2&&Math.abs(z-f.cz)<f.d/2));
    }
    for(const stair of SEA_STEPS){
      const footX=stair.x+stair.dx*2.66,footZ=stair.z+stair.dz*2.66;
      assert(!result.layoutFloors.some(f=>f.y===0&&Math.abs(footX-f.cx)<f.w/2-.01&&Math.abs(footZ-f.cz)<f.d/2-.01),'Sea stair must not end under another deck');
    }
    for(const z of [-14,0,14]){
      assert(result.site.elevation(0,z)<result.site.seaLevel);
      assert(result.site.elevation(HALL.west*BUILDING_SCALE,z)<result.site.seaLevel);
      assert(result.site.elevation(result.site.coastline(z)+15,z)<result.site.seaLevel);
    }
    let instances=0,triangles=0;
    const allObjects=[];scene.traverse(o=>allObjects.push(o));
    const backs=allObjects.filter(o=>o.geometry?.name==='Reclined wraparound seat shell');
    assert.equal(backs.length,1);assert.equal(backs[0].count,30);
    const dark=color=>Math.max(color.r,color.g,color.b)<.3;
    assert(dark(backs[0].material.color),'Chair shells must not be ivory');
    assert(!result.campus.roof);assert(!result.campus.setRoof);
    assert(dark(scene.getObjectByName('Fixed seminar acoustic ceiling').material.color));
    const pillows=allObjects.filter(o=>o.geometry?.name==='Aligned curved seat headrest');
    assert.equal(pillows.length,1);assert.equal(pillows[0].count,30);
    assert(dark(pillows[0].material.color),'Chair headrests must not stay white');
    const pillow=pillows[0].geometry.attributes.position,layer=pillow.count/2;
    for(let i=layer;i<pillow.count;i++){
      const x=pillow.getX(i),y=pillow.getY(i),z=pillow.getZ(i);
      const clothFront=-.30-(.18/.78)*(y-.60)+.17*(x/.52)**2+.11;
      assert(z-clothFront>.0049,'Headrest back must not penetrate curved upholstery');
    }
    for(let j=0;j<=10;j++)assert.equal(pillow.getY(j*21),pillow.getY(j*21+20),'Headrest has no sideways roll');
    const back=backs[0].geometry.attributes.position;
    assert(back.getZ(20)>back.getZ(10)+.15,'Seat sides wrap forward');
    assert(back.getZ(220)<back.getZ(10)-.17,'Seat top reclines backward');
    const platform=scene.getObjectByName('Unified platform top 0');assert(platform?.isMesh);
    assert(dark(platform.material.color),'Terrace base must remain dark stone');
    const fascia=scene.getObjectByName('Unified platform fascia 0').geometry.attributes.position;
    assert(Math.min(...Array.from({length:fascia.count},(_,i)=>fascia.getY(i)))<seaLevel,'Raised terrace skirt hides the underside above the sea');
    const cells=platform.userData.cells;
    for(let i=0;i<cells.length;i++)for(let j=i+1;j<cells.length;j++){
      const [a,b,c,d]=cells[i],[e,f,g,h]=cells[j];
      assert(Math.min(b,f)-Math.max(a,e)<1e-7||Math.min(d,h)-Math.max(c,g)<1e-7,'No coplanar overlapping platform tops');
    }
    for(const object of allObjects){
      if(!object.geometry)continue;
      assert([...object.geometry.attributes.position.array].every(Number.isFinite));
      if(object.isInstancedMesh){assert([...object.instanceMatrix.array].every(Number.isFinite));instances+=object.count;}
      if(object.isMesh)triangles+=(object.geometry.index?.count || object.geometry.attributes.position.count)/3*(object.isInstancedMesh?object.count:1);
    }
    console.log(JSON.stringify({sceneObjects:scene.children.length,instances,triangles,forestTrees:result.landscape.plantings.length}));
    assert(instances>1500);assert(triangles<1300000,`Expanded garden and auditorium must stay within the 1.3M scene budget: ${triangles}`);
    assert(scene.children.filter(o=>o.isMesh).length<330,'Spatial instancing must bound model draw batches');
    for(const name of ['Continuous mountain ridges','Detailed coastal terrain','Connected waterfall and winding creek','Mossy waterfall buttresses','Weathered coastal outcrops'])assert(!scene.getObjectByName(name),name+' must be removed');
    for(const name of ['Giant tree crowns','Jointed bamboo stems','Bamboo leaf sprays','Soft lawn garden','Garden flower borders','Palm fronds','Fern understory'])assert(scene.getObjectByName(name),name);
    assert.equal(result.landscape.plantings.length,0);
    assert.equal(scene.getObjectByName('Offshore planted garden trays').userData.exposedPiles,false);
    // No long vertical pile is left below any platform.
    for(const o of allObjects.filter(o=>o.isInstancedMesh&&o.geometry.type==='BoxGeometry')){
      const matrix=new Three.Matrix4(),p=new Three.Vector3(),q=new Three.Quaternion(),scale=new Three.Vector3();
      for(let i=0;i<o.count;i++){o.getMatrixAt(i,matrix);matrix.decompose(p,q,scale);assert(!(p.y<-1&&scale.y>3),'Exposed support pile survived');}
    }
    const m=scene.getObjectByName('Giant tree crowns').material,shader={uniforms:{},vertexShader:Three.ShaderLib.standard.vertexShader,fragmentShader:Three.ShaderLib.standard.fragmentShader};
    m.onBeforeCompile(shader);assert(shader.vertexShader.includes('float sway='));
    result.landscape.update(.016);result.landscape.update(-1);
    assert(result.materials.pale.normalMap.isDataTexture);assert(result.materials.steel.roughnessMap.isDataTexture);
    assert(result.materials.pale.normalMap.generateMipmaps);assert(result.materials.timber.normalMap);
    assert(calls.includes('NS 方程 · 存在性与光滑性'));assert(calls.includes('Hodge 猜想 ？'));assert(calls.includes('数学难民营'));
    assert(calls.includes('NS'));assert.equal(clippedFragments,12);
    assert.equal(calls.filter(t=>t==='数学难民营').length,1);assert(calls.includes('报告厅'));assert(calls.includes('图书馆'));
    assert(!scene.getObjectByName('Sea terrace chaise lounges'));
    assert.equal(scene.getObjectByName('Expanded sea lounge terrace').userData.pool,false);
    const hall=scene.getObjectByName('Two-storey seminar hall').userData;
    assert(hall.fixedRoof&&hall.storeys===2&&hall.stairSteps===34);
    assert(hall.riserMetres>.14&&hall.riserMetres<.18);
    assert(scene.getObjectByName('Upper seminar lounge'));
    assert.deepEqual(scene.getObjectByName('Coffee machine').userData,{groupHeads:2,cups:2,hoppers:2,architectureScale:BUILDING_SCALE});
    assert(scene.getObjectByName('Coffee cabin sign'));assert(calls.includes('咖啡小屋'));
    for(let i=1;i<=3;i++)assert(scene.getObjectByName('Module arch bridge '+i));
    const glazing=scene.getObjectByName('Four-panel smart seminar glazing').userData;
    assert.equal(glazing.panels,4);assert.equal(glazing.joints,3);assert(glazing.sealMetres<=.008);
    const smart=scene.children.filter(o=>o.isInstancedMesh&&o.material===result.materials.smartGlass);assert.equal(smart.length,1);assert.equal(smart[0].count,4);
    result.setTime(12,true);assert(scene.fog.density<=.0003);
    const sky=scene.children.find(o=>o.material?.uniforms?.turbidity);
    assert(sky.material.uniforms.turbidity.value<=2);
    assert.equal(scene.children.filter(o=>o.name.startsWith('Framed specimen tree')).length,ORNAMENTAL_TREES.length);
    for(const f of result.layoutFloors.filter(f=>f.y===0))assert(elevation(f.cx,f.cz)<seaLevel);
    for(const name of ['NS conjecture blackboard','Hodge conjecture blackboard','Entrance lintel sign','Entrance wayfinding sign'])assert(scene.getObjectByName(name)?.isMesh,name);
    assert(!calls.some(text=>text.includes('已解决')));
    assert(result.ocean.material.uniforms.time);assert.equal(typeof result.lighting,'function');
    result.lighting(0,true);result.lighting(100,true);result.dispose();
    assert(result.ocean.material.uniforms.sunDirection.value.toArray().every(Number.isFinite));
  }finally{delete globalThis.__retreatTestThree;delete globalThis.document;}
});

test('entire site is open sea with a constant submerged seabed',()=>{
  for(let x=-600;x<=600;x+=20)for(let z=-600;z<=600;z+=20){assert.equal(elevation(x,z),-15);assert.equal(slope(x,z),0);assert(!canPlant(x,z));}
  assert.equal(shoreline(0),null);assert(seaLevel<DECK_Y);assert(DECK_Y-seaLevel<1);
});

test('camera eye and orbit target never enter the ocean',()=>{
  const camera=new Three.PerspectiveCamera(50,1,.08,12000),target=new Three.Vector3();
  const water=seaLevel*BUILDING_SCALE;
  for(const eye of [-100,-1,0,1,2,20])for(const aim of [-100,0,2]){
    camera.position.set(5,eye,8);target.set(0,aim,0);constrainAboveWater(camera,target,water);
    assert(camera.position.y>=water+1);assert(target.y>=water+.05);assert(camera.quaternion.toArray().every(Number.isFinite));
  }
  for(const shot of SHOTS)for(const p of shot.positions)assert(p[1]>=water+1);
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
  const inkRows=[[80,40,500,70],[100,180,800,100]],path=erasingPlan(null,inkRows);
  const wipes=Array.from({length:701},(_,i)=>eraserPose(i/700,1536,640,path)).filter(p=>p.contact);
  for(const [a,b,w,h] of inkRows)for(let y=b;y<=b+h;y+=10)for(let x=a;x<=a+w;x+=10){
    assert(wipes.some(p=>{const dx=x-p.x,dy=y-p.y,c=Math.cos(p.angle),s=Math.sin(p.angle);return Math.abs(dx*c+dy*s)<=ERASER_HALF_WIDTH&&Math.abs(-dx*s+dy*c)<=ERASER_HALF_HEIGHT;}),'Tilted wipe must cover every ink-bearing row');
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

test('Consolidated local SVG pages preserve notebook formula content and stay within the board',async()=>{
  const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/pages.json',import.meta.url),'utf8'));
  assert(pages.length<40);assert(pages.some(p=>p.source.startsWith('§ 3.')));assert(pages.some(p=>p.source.startsWith('§ 4.')));
  assert.equal(new Set(pages.map(p=>p.tex)).size,pages.length);assert.equal(new Set(pages.map(p=>p.text)).size,pages.length);
  assert(pages.every(p=>/^§ /.test(p.source)));assert(pages.every(p=>p.rows[2][3]<=(p.diagram?336:301)));
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
  source=source.replace('./chalk-language.js?v=18-board-diagrams',new URL('./chalk-language.js',import.meta.url).href).replace("from 'three'",`from '${core}'`).replace('./lecture-state.js?v=18-board-diagrams',state).replace('./chalk-motion.js?v=18-board-diagrams',new URL('./chalk-motion.js',import.meta.url).href);
  const originalFetch=globalThis.fetch,originalImage=globalThis.Image,originalDocument=globalThis.document;
  const contexts=[];
  globalThis.document={createElement:()=>({width:0,height:0,getContext(){
    const ctx={clearRect(){},fillText(){},measureText(t){return {width:[...t].length*24};},drawImage(){},fillRect(){},save(){},restore(){},beginPath(){},rect(){},clip(){},translate(){},rotate(){}};contexts.push(ctx);return ctx;
  }})};
  globalThis.Image=class{set src(value){this.url=value;queueMicrotask(()=>this.onload());}};
  globalThis.fetch=async()=>({ok:true,json:async()=>JSON.parse(await fs.readFile(new URL('./assets/chalk/pages.json',import.meta.url),'utf8'))});
  try{
    const {createLecture}=await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
    const scene=new Three.Scene(),lecture=await createLecture(scene,{capabilities:{getMaxAnisotropy:()=>8}});
    const boards=scene.children.filter(o=>o.name.startsWith('Sliding chalkboard'));
    await lecture.setLanguage('en');assert.equal(lecture.language,'en');assert(lecture.copy(0).title.toLowerCase().includes('double complex'));await lecture.setLanguage('zh');
    assert.equal(boards.length,6);assert.equal(new Set(boards.map(b=>b.children[0].material.map.uuid)).size,6);
    for(const board of boards){const m=board.children[0].material;assert.equal(m.emissiveIntensity,0);assert.equal(m.specularIntensity,0);assert.equal(m.roughness,1);assert.equal(m.envMapIntensity,0);}
    assert.deepEqual(lecture.consoleButtons.map(b=>b.userData.action),['language']);
    const layoutRoot=new Three.Group();configureLectureRoot(layoutRoot);layoutRoot.updateMatrixWorld(true);
    for(const b of lecture.consoleButtons){const h=layoutRoot.localToWorld(b.position.clone()).y-DECK_Y*BUILDING_SCALE;assert(h>1.1&&h<1.8,'Buttons remain reachable after boards are raised');}
    const button=lecture.consoleButtons[0],rest=button.position.z;button.userData.pressed=true;lecture.update(.1);assert.equal(button.position.z,rest);assert(button.material.opacity>.035);assert(button.userData.smartGlass);button.userData.pressed=false;
    lecture.setConsoleState();assert(lecture.consoleButtons[0].userData.lastLabel);
    assert(button.userData.singleToggle);
    const touchPosition=layoutRoot.localToWorld(button.position.clone()),halfWidth=button.geometry.parameters.width*.72/2;
    assert(touchPosition.z-halfWidth>5*BUILDING_SCALE+.5,'Entire control is inside the outer glass pane');
    assert(touchPosition.z+halfWidth<10*BUILDING_SCALE-.5,'Control stays clear of the perimeter');
    assert(touchPosition.z-halfWidth>6.2+2,'Control clears the complete board assembly');
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
    lecture.select(lecture.pages.length-1);await Promise.resolve();lecture.staticPage();lecture.update(.1,true);
    assert.equal(lecture.clock.page,lecture.pages.length-1);assert.equal(lecture.clock.slots[lecture.clock.active].progress,1);
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
    addEventListener(type,handler){this.events[type]=handler;},setAttribute(k,v){this.attributes[k]=v;},getAttribute(k){return this.attributes[k];},click(){this.events.click?.();}
  }]));
  globalThis.document={getElementById:id=>elements.get(id)};globalThis.innerWidth=390;globalThis.innerHeight=844;
  const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/pages.json',import.meta.url),'utf8'));
  const lecture={pages,clock:{page:0},playing:true};
  const source=(await fs.readFile(new URL('./chalk-reader.js',import.meta.url),'utf8')).replace('./chalk-typography.js?v=18-board-diagrams',new URL('./chalk-typography.js',import.meta.url).href).replace('./control-label.js?v=18-board-diagrams',new URL('./control-label.js',import.meta.url).href).replace('./display-profile.js?v=7-chalk-diagrams',new URL('./display-profile.js',import.meta.url).href);
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
  assert(/<header[\s\S]*id="fullscreen"[\s\S]*<\/header>/.test(html));
});
test('sparse ink gives short local eraser passes and proportional chalk timing',()=>{
  const width=1536,height=640,data=new Uint8ClampedArray(width*height*4);
  const regions=[[80,40,24,8],[1000,420,120,35]];
  for(const [x,y,w,h] of regions)for(let py=y;py<y+h;py++)for(let px=x;px<x+w;px++)data[(py*width+px)*4+3]=255;
  const image={data,width,height},path=erasingPlan(image);
  assert(path.duration<2,'Sparse writing should not cause a long empty-board wipe');
  for(const segment of path.segments.filter(s=>s.contact)){
    assert(Math.abs(segment.a[0]-segment.b[0])<=160);
    assert(regions.some(([x,y,w,h])=>segment.a[0]>=x-32&&segment.a[0]<=x+w+32&&segment.a[1]>=y-28&&segment.a[1]<=y+h+28));
  }
  const poses=Array.from({length:701},(_,i)=>eraserPose(i/700,width,height,path)).filter(p=>p.contact);
  for(const [x,y,w,h] of regions)for(let py=y;py<y+h;py+=2)for(let px=x;px<x+w;px+=2)
    assert(poses.some(p=>{const dx=px-p.x,dy=py-p.y,c=Math.cos(p.angle),s=Math.sin(p.angle);return Math.abs(dx*c+dy*s)<=ERASER_HALF_WIDTH&&Math.abs(-dx*s+dy*c)<=ERASER_HALF_HEIGHT;}));
  const rows=[[0,0,20,20],[0,40,1000,20]],plan=writingPlan(rows);
  const short=plan.segments.filter(s=>s.row===0).reduce((sum,s)=>sum+s.cost,0);
  assert(short/plan.total<.05,'A short equation must not take the same time as a full line');
  const clock=new LectureClock(10);clock.setDurations(0,{write:2,erase:1});clock.startWrite();
  assert.equal(clock.duration,2);clock.slots[clock.active].page=0;clock.page=6;clock.phase='erase';assert.equal(clock.duration,1);
});
test('tour resume blends from current view without a blackout or teleport',async()=>{
  const source=await fs.readFile(new URL('./app.js',import.meta.url),'utf8');
  const resume=source.slice(source.indexOf('function resumeTour'),source.indexOf('function applyShot'));
  assert(resume.includes('camera.position.clone()')&&resume.includes('controls.target.clone()'));
  assert(resume.includes('controls.enableDamping=false')&&resume.includes('suppressFadeShot=shot'));
  const apply=source.slice(source.indexOf('function applyShot'),source.indexOf('function resize'));
  assert(apply.includes('lerpVectors(blend.position,position,k)'));
  assert(!apply.includes('Math.sin(k*Math.PI)'));
  assert(apply.includes('suppressFadeShot===shot?0'));
  let previous=0;for(let i=0;i<=100;i++){const k=smoothProgress(i/100);assert(k>=previous&&k-previous<.02);previous=k;}
});

test('manual board viewing yields after the configured idle time without restarting a tour',async()=>{
  const {BoardFollow}=await import('./board-follow.js');let now=0;
  const follow=new BoardFollow(20,()=>now);assert(follow.following);
  follow.begin();now=45;assert(!follow.following,'A held drag never times out');
  follow.end();now=64.99;assert(!follow.following);now=65;assert(follow.following);
  follow.touch();now=70;follow.touch();now=89;assert(!follow.following);now=90;assert(follow.following);
  follow.setDelay(5);follow.touch();now=94;assert(!follow.following);now=95;assert(follow.following);
  follow.setDelay(60);follow.touch();now=154;assert(!follow.following);now=155;assert(follow.following);
  follow.setDelay(100);assert.equal(follow.delay,60);follow.setDelay(1);assert.equal(follow.delay,5);
  follow.begin();follow.reset();assert(follow.following);
});

test('multiline formulas write one row at a time and lift before the next',async()=>{
  const {equationLines}=await import('./chalk-layout.mjs');
  assert.deepEqual(equationLines(String.raw`\begin{gathered}a=b\\[.35em]c=\frac{d}{e}\\f=g\end{gathered}`),['a=b',String.raw`c=\frac{d}{e}`,'f=g']);
  assert.equal(equationLines(String.raw`\frac{a+b}{c+d}`).length,1);
  const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/pages.json',import.meta.url),'utf8'));
  const page=pages.find(p=>p.source==='§ 1.8');assert.equal(page.formulaRows.length,3);
  const rows=page.formulaRows;
  for(let i=1;i<rows.length;i++)assert(rows[i-1][1]+rows[i-1][3]<rows[i][1]);
  const plan=writingPlan(rows);
  for(let i=0;i<rows.length;i++){
    const segment=plan.segments.find(s=>s.row===i&&s.contact),progress=(segment.start+segment.cost*.5)/plan.total;
    assert(inkReveal(rows,progress,i)>0);
    for(let j=i+1;j<rows.length;j++)assert.equal(inkReveal(rows,progress,j),0,'Later formulas must remain blank');
    if(i>0){const entering=plan.segments.find(s=>s.row===i&&s.entering);assert(entering&&!entering.contact);}
  }
});


test('inline mathematical letters, Unicode superscripts and operators always use print faces',async()=>{
  const {chalkRuns,chalkHTML,chalkSVG}=await import('./chalk-typography.js');
  for(const text of ['FᵖHⁿ','d²=0','Eᵣ','∂∂̄','𝓕','(−1)ᵖ','α→β','Kähler']){
    const runs=chalkRuns(text);assert(runs.every(run=>run.math),text);
    assert.equal(runs.map(run=>run.text).join(''),text);
    assert(chalkHTML(text).includes('class="chalk-math"'));
    assert(chalkSVG(text).includes('font-family="Times New Roman, serif"'));
  }
  assert.deepEqual(chalkRuns('设 X 为流形'),[{text:'设 ',math:false},{text:'X',math:true},{text:' 为流形',math:false}]);
  assert(!chalkHTML('<x>').includes('<x>'),'Text must remain escaped');
});


test('Chinese ink takes twice the contact time while mathematical ink keeps its pace',()=>{
 const base=[[0,0,100,30]],slow=[Object.assign([0,0,100,30],{chineseSpans:[[0,100]]})];
 const contact=p=>p.segments.filter(s=>s.contact).reduce((n,s)=>n+s.cost,0);
 assert.equal(contact(writingPlan(slow)),2*contact(writingPlan(base)));
 const mixed=[Object.assign([0,0,100,30],{chineseSpans:[[0,40]]})];
 assert(contact(writingPlan(mixed))>contact(writingPlan(base)));
 assert(contact(writingPlan(mixed))<contact(writingPlan(slow)));
});

test('diagram directions, board separation and bundled handwritten glyph coverage are valid',async()=>{
 const {diagramEdges}=await import('./chalk-diagrams.mjs');
 for(const e of diagramEdges('differential'))assert.deepEqual(e.to.map((x,i)=>x-e.from[i]),[2,-1]);
 for(const e of diagramEdges('zero'))assert.deepEqual(e.to.map((x,i)=>x-e.from[i]),[0,1]);
 const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/pages.json',import.meta.url),'utf8'));
 assert.equal(pages.filter(p=>p.diagram).length,6);
 for(const p of pages.filter(p=>p.diagram)){
   for(const [i,a] of p.formulaRows.entries())for(const b of p.formulaRows.slice(i+1)){
     assert(a[0]+a[2]<=b[0]||b[0]+b[2]<=a[0]||a[1]+a[3]<=b[1]||b[1]+b[3]<=a[1],'Independent ink regions cannot overlap');
   }
   assert(p.formulaRows.every(r=>r[1]+r[3]<448),'Diagram must clear the prose');
 }
 const coverage=JSON.parse(await fs.readFile(new URL('./assets/fonts/chalk-coverage.json',import.meta.url),'utf8'));
 for(const p of pages)for(const c of p.source+p.title+p.text)if(/[\u3400-\u9fff]/.test(c))assert(coverage.characters.includes(c),'Missing handwritten character '+c);
 const {createHash}=await import('node:crypto');
 assert.equal(createHash('sha256').update(await fs.readFile(new URL('./assets/fonts/RefugeChinese.woff2',import.meta.url))).digest('hex'),coverage.sha256);
});

test('room fill uses bounded reflected irradiance and chalk tip sits above its shaft',async()=>{
 const {createRoomFill}=await import('./room-fill.js');
 const fill=createRoomFill(),m=new Three.MeshStandardMaterial(),root=new Three.Group();root.add(new Three.Mesh(new Three.BoxGeometry(),m));fill.apply(root);
 const shader={uniforms:{},vertexShader:'#include <project_vertex>',fragmentShader:'#include <lights_fragment_maps>'};m.onBeforeCompile(shader,{});
 assert(shader.vertexShader.includes('instanceMatrix*seminarVertex'));assert(shader.fragmentShader.includes('roomMask'));assert(shader.fragmentShader.includes('irradiance+='));assert.equal(m.emissiveIntensity,1);assert.equal(m.emissive.getHex(),0);
 fill.setDaylight(1);const day=fill.strength.value;fill.setDaylight(0);assert(fill.strength.value>day);
 const source=await fs.readFile(new URL('./lecture.js',import.meta.url),'utf8');
 const axis=source.match(/const chalkAxis=new THREE.Vector3\(([^)]+)\)/)[1].split(',').map(Number);
 assert(axis[1]<0&&axis[2]>0,'The shaft must slope down and away from the anchored writing tip');
});
