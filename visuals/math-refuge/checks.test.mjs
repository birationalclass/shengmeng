import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {SHOTS,smoothProgress,advanceShot,OPENING_OVERVIEW_MS,transitionSeconds} from './camera-paths.js?v=37-speaker';
import * as Three from '../3d/vendor/three.module.js';
import {LectureClock,boardSlot,boardHeights,BOARD_LAYOUT} from './lecture-state.js';
import {configureCameraInput,DEFAULT_ROTATION} from './camera-input.js';
import {displayProfile,boardFraming,readingFormulaWidth} from './display-profile.js';
import {elevation,coastline,shoreline,canPlant,slope,seaLevel} from './landscape-shape.js?v=36-board-detail';
import {createHash} from 'node:crypto';
import {bindCameraIntent} from './camera-intent.js';
import {BUILDING_SCALE,riverPoint,watercourse,LAWNS,GIANT_TREES,BAMBOO_GROVES,POOL_RECTS,poolTopology,inPool,inBuilding,BRIDGES,COURT_DECKS,COFFEE_PAD,SEA_TERRACE,SEA_STEPS,DISTANT_ISLANDS,HALL,DECK_Y,configureLectureRoot,lectureViewOffset,LECTURE_SCALE,ROOM_PADS,GARDEN_PADS,ORNAMENTAL_TREES} from './site-layout.js?v=36-board-detail';
import {writingPlan,erasingPlan,writingPose,inkReveal,rowReveal,eraserPose,wetOpacity,chalkLength,inkGuides,ERASER_HALF_WIDTH,ERASER_HALF_HEIGHT} from './chalk-motion.js?v=22-handwritten-cover';
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
    const copy=chalkCopy(p,lang);assert(copy.title&&(copy.text||p.kind==='closing'));
    if(lang==='en')assert(!/[\u3400-\u9fff]/.test(copy.title+copy.text+copy.source));
    const rows=composeChalkPage(ctx,p,i,lang,{});
    for(const [x,y,w,h] of rows){assert(x>=0&&y>=0&&x+w<=1536&&y+h<=620);}
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
  assert(SEA_TERRACE[1]===54&&SEA_TERRACE[1]>HALL.east);
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


test('finite camera destinations include all buildings, upstairs, ocean and garden views',()=>{
  assert.equal(SHOTS.length,18);assert(SHOTS.some(s=>s.lecture));assert(SHOTS.some(s=>s.name==='海景露台'));assert(SHOTS.some(s=>s.name==='海上花园'));assert(SHOTS.some(s=>s.name==='二楼客厅'));
  for(const shot of SHOTS){
    assert(shot.duration>=20);assert(shot.fov>30&&shot.fov<70);
    for(const points of [shot.positions,shot.targets]){
      const curve=new Three.CatmullRomCurve3(points.map(p=>new Three.Vector3(...p)));
      for(let i=0;i<=100;i++)assert(curve.getPointAt(smoothProgress(i/100)).toArray().every(Number.isFinite));
    }
  }
  assert(SHOTS[0].lecture);assert.equal(OPENING_OVERVIEW_MS,5000);assert(transitionSeconds(100)>transitionSeconds(1));assert.equal(transitionSeconds(0),4.4);assert.equal(transitionSeconds(200),13);
  const wrap=advanceShot(SHOTS.length-1,SHOTS.at(-1).duration-.02,.05,1);assert.equal(wrap.index,0);assert(wrap.time>=0&&wrap.time<.1);
  assert.deepEqual(advanceShot(0,1,-5,1),{index:0,time:1});
});

test('all page and JavaScript local asset references resolve',async()=>{
  const root=new URL('./',import.meta.url);
  for(const file of ['index.html','app.js?v=43-tight-boards','scene.js?v=42-warm-seating','camera-paths.js?v=37-speaker','lecture.js','lecture-state.js','chalk-reader.js','display-profile.js','surface-materials.js','landscape.js?v=36-board-detail','landscape-shape.js?v=36-board-detail']){
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
  const app=await fs.readFile(new URL('app.js?v=43-tight-boards',root),'utf8');
  for(const file of ['app.js?v=43-tight-boards','chalk-reader.js']){
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
  const sceneModule=await inlineAddon('./scene.js?v=42-warm-seating');
  const calls=[];let clippedFragments=0;
  globalThis.__retreatTestThree={...Three,
    TextureLoader:class{async loadAsync(){const texture=new Three.Texture();texture.image={width:256,height:256};return texture;}},
    PMREMGenerator:class{fromScene(){return {texture:new Three.Texture(),dispose(){}};}dispose(){}}
  };
  globalThis.document={createElement:()=>({width:0,height:0,getContext:()=>({fillRect(){},fillText(text){calls.push(text);},save(){},restore(){},translate(){},rotate(){},beginPath(){},arc(){},fill(){},moveTo(){},lineTo(){},closePath(){},clip(){clippedFragments++;},drawImage(){}})})};
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
    assert.equal(auditorium.userData.rows,3);assert.equal(HALL.south-HALL.north,23);
    const tiers=scene.children.filter(o=>o.name.startsWith('Carpeted seating tier '));
    for(const tier of tiers){
      const bounds=new Three.Box3().setFromObject(tier);
      assert((HALL.south*BUILDING_SCALE-bounds.max.z)>2.3,'South entrance has a flat passage before the seating tiers');
      assert((bounds.min.z-HALL.north*BUILDING_SCALE)>2.3,'North entrance has a flat passage before the seating tiers');
    }
    const hallGuard=scene.getObjectByName('Hall complete upper guard').userData;
    const onSlab=(x,z)=>hallGuard.rectangles.some(([a,b,c,d])=>x>=a&&x<=b&&z>=c&&z<=d);
    for(const rail of scene.children.filter(o=>o.name.startsWith('Hall complete upper guard edge '))){
      for(const [x,y,z] of rail.userData.anchors)for(const dx of [-.0525,.0525])for(const dz of [-.0525,.0525]){
        assert(onSlab(x+dx,z+dz),'Entire square railing base stays on the upper slab');
      }
    }
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
    assert(scene.getObjectByName('Modern interactive seminar lectern'));assert.equal(auditorium.userData.architectureScale,BUILDING_SCALE);
    assert(Math.abs(BUILDING_SCALE**2-2)<1e-12);
    assert(auditorium.userData.seatPositions.every(p=>p[0]>HALL.west&&p[0]<HALL.boardX&&Math.abs(p[2])>=.75));
    assert.equal(auditorium.userData.clearHeight,4.9);assert(auditorium.userData.offshore);
    assert.equal(scene.children.filter(o=>o.name.startsWith('Small arch bridge ')).length,0);
    assert.equal(scene.children.filter(o=>o.name.startsWith('Level pool crossing ')).length,0);
    assert.equal(scene.getObjectByName('Low sea-facing seminar hall').userData.clearHeight,4.9);
    assert.equal(result.campus.lightingZones.filter(z=>z.task==='blackboard').length,3);
    for(const name of ['Upper private studies','Upper small seminar','Upper seminar lounge'])assert(result.campus.lightingZones.some(z=>z.name===name));
    assert.equal(result.pathLighting.count,25);const lanterns=scene.children.filter(o=>o.name.startsWith('Platform path lantern '));assert.equal(new Set(lanterns.map(o=>o.userData.type)).size,3);
    const spots=scene.children.filter(o=>o.isSpotLight);
    result.setTime(12);const daytime=spots.map(o=>o.intensity);result.setTime(23);assert.equal(result.ocean.material.uniforms.nightVisibility.value,.06);
    spots.forEach((lamp,i)=>{assert(lamp.intensity>daytime[i]);assert(lamp.distance>0&&lamp.intensity>60);});
    for(const name of ['Academic living villa','Discussion villa','Upper private studies','Upper small seminar','Independent quiet library','Quiet residential villa 1','Quiet residential villa 2','Service and tea kitchen','Seminar hall','Bamboo tea pavilion'])assert(scene.getObjectByName(name+' light fixtures'));
    for(const lamp of scene.children.filter(o=>o.isSpotLight)){assert(lamp.position.y>lamp.target.position.y);assert.equal(lamp.penumbra,.85);assert(!lamp.castShadow);}
    const fills=scene.children.filter(o=>o.isPointLight);assert.equal(fills.length,4);
    for(const lamp of fills){assert(!lamp.castShadow);assert.equal(lamp.userData.task,'seminar-fill');assert(lamp.position.x>HALL.west*BUILDING_SCALE&&lamp.position.x<HALL.east*BUILDING_SCALE);assert(lamp.intensity>0&&lamp.distance<16);}
    for(const name of ['Connected infinity pool and core water court','East infinity overflow sheet','Side infinity overflow sheet','Sunrise infinity edge'])assert(!scene.getObjectByName(name));
    assert.equal(result.islands.group.children.length,4);assert.equal(result.sculptures.length,8);
    for(const island of result.islands.group.children){
      const pos=island.geometry.attributes.position;
      for(let i=1;i<=96;i++)assert.equal(pos.getY(i),pos.getY(0),'Island pole must not split into vertical spikes');
      assert([...island.geometry.attributes.normal.array].every(Number.isFinite));
    }
    for(const sculpture of result.sculptures){
      assert(result.layoutFloors.some(f=>f.y===0&&Math.abs(sculpture.position.x/BUILDING_SCALE-f.cx)+1.3<=f.w/2+.001&&Math.abs(sculpture.position.z/BUILDING_SCALE-f.cz)+1.3<=f.d/2+.001),'Each sculpture needs a complete dry pedestal pad: '+sculpture.name);
    }
    assert.equal(new Set(result.sculptures.map(o=>o.userData.facility)).size,8);
    const stairs=scene.children.filter(o=>o.name.startsWith('Sea access stair '));assert.equal(stairs.length,0);assert.equal(SEA_STEPS.length,0);
    assert(!scene.getObjectByName('Coffee cabin mathematical sculpture'));assert(scene.getObjectByName('Library open book sculpture').userData.openBook);
    assert(!LAWNS.some(l=>l.z===34));assert(!GARDEN_PADS.some(r=>r[0]===-22&&r[2]===29));
    const [tw,te,tn,ts]=SEA_TERRACE;assert(result.layoutFloors.some(f=>f.y===0&&f.cx-f.w/2===tw&&f.cx+f.w/2===te&&f.cz-f.d/2===tn&&f.cz+f.d/2===ts),'Hall platform must match the declared paving bounds');
    assert.equal(result.fleet.boats.filter(b=>b.userData.type==='sail').length,3);assert.equal(result.fleet.boats.filter(b=>b.userData.type==='kayak').length,2);
    for(let i=0;i<100;i++)result.fleet.update(.1);for(const boat of result.fleet.boats){assert(Math.abs(boat.position.y-result.site.seaLevel)<.1);assert(!result.layoutFloors.some(f=>f.y===0&&Math.abs(boat.position.x/BUILDING_SCALE-f.cx)<f.w/2+3&&Math.abs(boat.position.z/BUILDING_SCALE-f.cz)<f.d/2+3));}
    for(const name of ['Villa exterior stair','Hall exterior stair']){
      const d=scene.getObjectByName(name).userData;
      const landing=result.layoutFloors.find(f=>Math.abs(f.y-d.rise)<1e-8&&Math.abs(d.x-f.cx)<f.w/2&&Math.abs(d.landingZ-f.cz)<f.d/2);
      assert(landing,'Stair arrives on a connected landing');
      assert(d.lastZ-d.tread/2>=landing.cz+landing.d/2-.03,'Raised landing must not bury the last few steps');
      for(const side of [-1,1]){
        const rail=scene.getObjectByName(name+' rail '+side).userData;
        assert(rail.anchors.length>10);
        for(const [i,p] of rail.anchors.entries()){
          assert(Math.abs(p[0]-d.x)+.0525<d.width/2,'Post footplate must fit on the tread');
          const step=Math.round((d.startZ-p[2])/d.tread),onLanding=i===rail.anchors.length-1;
          assert(Math.abs(p[1]-(DECK_Y+d.rise*(onLanding?1:(step+1)/d.count)))<1e-8,'Post foot meets tread height');
          assert.deepEqual(rail.tops[i],[p[0],p[1]+rail.height,p[2]],'Handrail connects to the post cap');
        }
      }
    }
    const entrance=scene.getObjectByName('Centered upper hall entrance').userData;
    assert.equal(entrance.doorCenterZ,entrance.landingCenterZ);assert.equal(entrance.supportColumns,0);
    assert(entrance.treadMetres>.32&&entrance.treadMetres<.38);
    const hallFlight=scene.getObjectByName('Hall exterior stair').userData;
    assert(hallFlight.startZ+hallFlight.tread/2<HALL.south,'Centered upper entrance must not push the stair foot into the route');
    const supportMatrix=new Three.Matrix4(),supportPosition=new Three.Vector3(),supportScale=new Three.Vector3(),supportRotation=new Three.Quaternion();
    for(const mesh of scene.children.filter(o=>o.isInstancedMesh&&o.material===result.materials.steel))for(let i=0;i<mesh.count;i++){
      mesh.getMatrixAt(i,supportMatrix);supportMatrix.decompose(supportPosition,supportRotation,supportScale);
      assert(!(supportPosition.x>32.4&&supportPosition.x<33.1&&Math.abs(supportPosition.z)<3&&supportPosition.y<3&&supportScale.y>2),'No tall column beneath the hall landing');
    }
    for(const stair of stairs){const d=stair.userData;assert.equal(d.steps,7);assert(d.riserMetres>.15&&d.riserMetres<.2);assert(d.treadMetres>.5);assert(Math.abs(d.heights.at(-1)-seaLevel-.025)<1e-8);for(let i=1;i<d.heights.length;i++)assert(d.heights[i]<d.heights[i-1]);}
    assert(scene.getObjectByName('Independent quiet library'));assert(scene.getObjectByName('Quiet residential villa 1'));assert(scene.getObjectByName('Quiet residential villa 2'));
    const roofNumbers=[];scene.traverse(o=>{if(o.userData.roofNumber)roofNumbers.push(o);});
    assert.deepEqual(roofNumbers.map(o=>o.userData.roofNumber).sort((a,b)=>a-b),[1,2,3,4,5,6,7,8,9]);
    for(const o of roofNumbers){assert.equal(o.rotation.x,-Math.PI/2);assert(o.material.transparent&&!o.material.depthWrite);assert(o.geometry.parameters.width<=Math.min(o.userData.roof.width,o.userData.roof.depth));}
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
    assert.equal(backs.reduce((n,b)=>n+b.count,0),66);assert(backs.length>=4,'Separate floors must be culled independently');
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
    assert(scene.children.filter(o=>o.isMesh).length<550,'Spatial instancing must bound model draw batches');
    const batches=scene.children.filter(o=>o.isInstancedMesh),originalGeometry=new Map(batches.map(m=>[m,m.geometry]));
    const view=new Three.PerspectiveCamera(55,16/9,.2,12000);
    for(const distance of [40,61,66,120,350,800]){
      view.position.set(-distance,30,distance);result.updateGeometryLOD(view,1080);
      assert(batches.every(m=>m.visible),'No architectural instance batch may disappear when the camera retreats');
      for(const mesh of batches){
        const original=originalGeometry.get(mesh);
        if(original.type!=='RoundedBoxGeometry')assert.equal(mesh.geometry,original,'Stair treads, rails and structural boxes keep their geometry');
        else{mesh.geometry.computeBoundingBox();original.computeBoundingBox();assert(mesh.geometry.boundingBox.min.distanceTo(original.boundingBox.min)<1e-5);assert(mesh.geometry.boundingBox.max.distanceTo(original.boundingBox.max)<1e-5);}
      }
    }
    assert(batches.some(m=>m.userData.lodLevel===1),'Far rounded furniture uses lower tessellation, not an absent model');
    const farTriangles=batches.reduce((n,m)=>n+(m.geometry.index?.count||m.geometry.attributes.position.count)/3*m.count,0);
    const fullTriangles=batches.reduce((n,m)=>{const g=originalGeometry.get(m);return n+(g.index?.count||g.attributes.position.count)/3*m.count;},0);
    assert(farTriangles<fullTriangles,'Far rounded LOD must reduce vertex work');
    for(const mesh of batches.filter(m=>m.userData.lodLevel===1)){const high=originalGeometry.get(mesh);assert(mesh.geometry.attributes.position.count<high.attributes.position.count*.4,'Rounded corners use substantially fewer vertices');}
    console.log(JSON.stringify({architecturalTriangles:fullTriangles,farLodTriangles:farTriangles,allBatchesVisible:true}));
    for(const mesh of batches){mesh.geometry=originalGeometry.get(mesh);mesh.userData.lodLevel=0;}

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
    const blindBounds=new Three.Box3().setFromObject(result.campus.blind);
    assert(blindBounds.min.x>(HALL.east+.035/2)*BUILDING_SCALE,'Optional blind stays behind the glass, not inside relocated boards');
    const lounge=scene.getObjectByName('Upper sea-view academic lounge A');assert(lounge);
    const stations=lounge.getObjectByName('Six color iMac workstations').userData.stations;
    assert.equal(stations.length,6);assert.equal(new Set(stations.map(s=>s.color)).size,6);
    assert.equal(new Set(stations.map(s=>s.deskColor)).size,1);assert.equal(new Set(stations.map(s=>s.chairColor)).size,1);
    assert(stations.every(s=>s.x<0&&Math.abs(s.z)>2));
    assert(lounge.getObjectByName('Floor-standing lounge plants').userData.plants.every(p=>p.y===0));
    lounge.updateWorldMatrix(true,true);
    for(const station of stations){
      assert.equal(station.computerWidth,.547);assert.equal(station.computerHeight,.461);assert(station.bodyDepth<.012);
      const transform=v=>v.applyAxisAngle(new Three.Vector3(0,1,0),Math.PI/2).add(new Three.Vector3(station.x,0,station.z)).applyMatrix4(lounge.matrixWorld);
      const eye=transform(new Three.Vector3(0,1.19,.55));
      for(const u of [-.98,-.5,0,.5,.98])for(const v of [-.98,-.5,0,.5,.98]){
        const target=transform(new Three.Vector3(station.screen[0]+u*station.screenSize[0]/2,station.screen[1]+v*station.screenSize[1]/2,station.screen[2]));
        const hits=new Three.Raycaster(eye,target.clone().sub(eye).normalize()).intersectObject(lounge,true);
        assert.equal(hits[0]?.object.material.name,'Unobstructed iMac display','Stand and chassis must not occlude any screen sample');
      }
    }
    const circles=lounge.getObjectByName('Three sea-facing discussion circles').userData.discussions;
    assert.equal(circles.length,3);assert(circles.every(s=>s.x>0&&s.opening==='west'));
    assert(circles.every(s=>!s.visitorChair&&!s.tablePlant));
    assert(circles.every(s=>s.upholsteryColor==='776352'&&s.shellColor==='544e45'));
    for(const name of ['Lounge warm upholstered back','Lounge warm seat cushions']){
      const mesh=lounge.children.find(o=>o.geometry?.name===name);
      assert.equal(mesh.material,pillows[0].material,'Upstairs upholstery reuses the exact hall fabric, not a similar paint');
      assert.equal(mesh.material.roughness,.97);assert(mesh.material.normalMap&&mesh.material.roughnessMap);
    }
    assert.equal(lounge.children.find(o=>o.geometry?.name==='Lounge dark seat shell').material,backs[0].material);
    const sofaPillows=lounge.children.find(o=>o.geometry?.type==='SphereGeometry'&&o.material===pillows[0].material);
    assert.equal(sofaPillows.count,15,'Every ring-sofa pillow uses the hall upholstery');
    for(const pod of circles){
      const origin=lounge.localToWorld(new Three.Vector3(pod.x-1.4,1.4,pod.z+.75));
      const hit=new Three.Raycaster(origin,new Three.Vector3(0,-1,0)).intersectObject(lounge,true)[0];
      assert(hit);assert(lounge.worldToLocal(hit.point.clone()).y<.07,'Former visitor-chair spot stays empty down to the rug');
    }
    for(let i=1;i<circles.length;i++)assert(circles[i].z-circles[i-1].z>circles[i].radius*2+.8);
    const loungeBar=lounge.getObjectByName('Tea coffee and drinks bar').userData;
    assert.equal(loungeBar.bottles,60);assert(loungeBar.bounds[3]<-7);assert(loungeBar.tea&&loungeBar.sink);
    const pose=result.campus.lectern.speakerPose(),lecternOrigin=result.campus.lectern.group.getWorldPosition(new Three.Vector3());
    assert(Math.abs(pose.position.y-lecternOrigin.y-1.68)<1e-8);assert(pose.position.x>lecternOrigin.x);
    assert(pose.target.x<pose.position.x);assert(pose.position.x<HALL.boardX*BUILDING_SCALE-.5);
    assert(scene.getObjectByName('Flexible gooseneck microphone'));assert(scene.getObjectByName('Embedded anti-glare touch display'));
    const loungerBounds=new Three.Box3().setFromObject(lounge);assert(loungerBounds.min.x>(39-3.5)*BUILDING_SCALE);assert(loungerBounds.max.x<(39+3.5)*BUILDING_SCALE);
    assert(loungerBounds.min.z>-6.5*BUILDING_SCALE);assert(loungerBounds.max.z<6.5*BUILDING_SCALE);
    assert.deepEqual(scene.getObjectByName('Coffee machine').userData,{groupHeads:2,cups:2,hoppers:2,architectureScale:BUILDING_SCALE});
    assert(scene.getObjectByName('Coffee cabin sign'));assert(calls.includes('咖啡小屋'));
    for(let i=1;i<=3;i++)assert(scene.getObjectByName('Module arch bridge '+i));
    const glazing=scene.getObjectByName('Seamless smart seminar glazing').userData;
    assert.equal(glazing.panels,1);assert.equal(glazing.joints,0);assert(glazing.sealMetres<=.008);
    const smart=scene.children.filter(o=>o.isInstancedMesh&&o.material===result.materials.smartGlass);assert.equal(smart.reduce((n,b)=>n+b.count,0),12);
    for(const {group,leaves} of result.campus.automaticDoors.doors.filter(d=>!d.group.userData.side.startsWith('discussion-'))){
      group.updateWorldMatrix(true,true);
      assert(!group.userData.transom);assert.equal(group.userData.clearHeight,HALL.clearHeight/BUILDING_SCALE);
      for(const {leaf} of leaves){
        const pane=leaf.getObjectByName('Full-height sliding glass leaf'),bounds=new Three.Box3().setFromObject(pane);
        assert(Math.abs(bounds.min.y-DECK_Y*BUILDING_SCALE)<1e-6);
        assert(Math.abs(bounds.max.y-(DECK_Y*BUILDING_SCALE+HALL.clearHeight))<1e-6);
        assert(!leaf.getObjectByName('Door handle'),'Automatic glass doors have no protruding handles');
      }
      const rail=new Three.Box3().setFromObject(group.getObjectByName('Ceiling recessed door track'));
      assert(rail.min.y>DECK_Y*BUILDING_SCALE+HALL.clearHeight,'Track stays above the full-height doorway');
    }
    for(let level=0;level<3;level++){const room=scene.getObjectByName('Discussion classroom '+(level+1));assert.equal(room.userData.rows,2);assert.equal(scene.getObjectByName('Discussion classroom seats '+(level+1)).userData.seats,12);assert(room.userData.bounds[1]<HALL.west-80);}
    for(const flight of allObjects.filter(o=>o.name==='Seminar supported stair flight')){assert(flight.userData.riser>.14&&flight.userData.riser<.18);assert(flight.userData.tread>.25);}
    result.setTime(12,true);assert(scene.fog.density<=.0003);
    const sky=scene.getObjectByName('Continuous Shanghai sky');
    assert(sky.material.uniforms.radius.value>.004&&sky.material.uniforms.radius.value<.005);
    assert(sky.material.uniforms.day.value>.9);
    const environmentBefore=scene.environment;result.setTime(12.51,true);assert.equal(scene.environment,environmentBefore,'No half-hour reflection-map replacement');
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
  assert.equal(LAWNS.length,1);assert.equal(GIANT_TREES.length,3);assert.equal(BAMBOO_GROVES.length,3);
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

test('three pairs alternate six slots, erase reused boards and stop at the last page',()=>{
  assert.deepEqual(Array.from({length:6},(_,i)=>boardSlot(i)),[0,2,4,1,3,5]);
  for(let value=0;value<=1;value+=.05){const [a,b]=boardHeights(value);assert(Math.abs(a+b-BOARD_LAYOUT.low-BOARD_LAYOUT.high)<1e-9);assert(a>=BOARD_LAYOUT.low&&a<=BOARD_LAYOUT.high);assert(b>=BOARD_LAYOUT.low&&b<=BOARD_LAYOUT.high);}
  const clock=new LectureClock(65),phases=new Set(),slots=new Set();
  for(let step=0;step<3000;step++){clock.update(.1);phases.add(clock.phase);slots.add(clock.active);assert(clock.progress>=0&&clock.progress<=1);}
  assert.deepEqual([...phases].sort(),['erase','hold','lift','write']);assert.equal(slots.size,6);
  clock.select(64);clock.next();assert.equal(clock.page,64);clock.next(-1);assert.equal(clock.page,63);clock.select(0);clock.next(-1);assert.equal(clock.page,0);
  clock.select(4);clock.startWrite();assert.equal(clock.slots[clock.active].page,4);assert.equal(clock.slots[clock.active].progress,0);
  const elapsed=clock.elapsed;clock.update(-1);assert.equal(clock.elapsed,elapsed);
});

test('Consolidated local SVG pages preserve notebook formula content and stay within the board',async()=>{
  const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/pages.json',import.meta.url),'utf8'));
  assert(pages.length<40);assert(pages.some(p=>p.source.startsWith('§ 3.')));assert(pages.some(p=>p.source.startsWith('§ 4.')));
  assert.equal(new Set(pages.filter(p=>!p.kind).map(p=>p.tex)).size,pages.filter(p=>!p.kind).length);assert.equal(new Set(pages.map(p=>p.text)).size,pages.length);
  assert(pages.every(p=>p.kind||/^§ /.test(p.source)));assert(pages.every(p=>p.rows[2][3]<=(p.layout==='flow'?640:p.diagram?336:301)));
  for(const page of pages){
    const svg=await fs.readFile(new URL(page.asset,import.meta.url),'utf8');
    const formula=await fs.readFile(new URL(page.formulaAsset,import.meta.url),'utf8');
    assert(page.kind||formula.includes('<path'));assert(!formula.includes('data-mjx-error'));assert(page.formulaEm>0);
    assert(page.kind||svg.includes('<path'));assert(!svg.includes('data-mjx-error'));assert(!svg.includes('<script'));
    assert(!/(?:href|src)="https?:/.test(svg));assert(page.kind||page.tex.length>0);
    for(const [x,y,w,h] of page.rows){assert(x>=0&&y>=0);assert(x+w<=1536&&y+h<=640);}
  }
  assert(pages.some(p=>p.tex.includes('\\delta_1\\delta_2+\\delta_2\\delta_1=0')));
  assert(pages.some(p=>p.tex.includes('\\operatorname{Gr}_F')));
  const html=await fs.readFile(new URL('./index.html',import.meta.url),'utf8');
  const {BUILDINGS,OUTDOOR_AREAS,buildingForShot}=await import('./building-catalog.js');
  const destinations=[...BUILDINGS.map(b=>b.shot),...OUTDOOR_AREAS].map(name=>SHOTS.find(s=>s.name===name));
  assert.equal(BUILDINGS.length,9);assert(destinations.every(Boolean));
  assert.equal(buildingForShot('二楼客厅').number,buildingForShot('报告厅').number);
  assert(BUILDINGS.every(b=>b.rooms.length&&b.rooms.every(r=>r.room!==undefined||SHOTS.some(s=>s.name===r.shot))));
  assert(destinations.every(s=>!s.lecture),'Board focus belongs to the room controls');
  assert(!html.slice(0,html.indexOf('</header>')).includes('seminarButton'),'Teaching building is a bottom destination');
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
  let source=await fs.readFile(new URL('./lecture.js',import.meta.url),'utf8');
  source=source.replace(/from '(\.\/[^'?]+)(?:\?[^']*)?'/g,(_,path)=>`from '${new URL(path,import.meta.url).href}'`).replace("from 'three'",`from '${core}'`);
  const originalFetch=globalThis.fetch,originalImage=globalThis.Image,originalDocument=globalThis.document;
  const contexts=[];
  globalThis.document={createElement:()=>({width:0,height:0,getContext(){
    const ctx={clearRect(){},fillText(){},measureText(t){return {width:[...t].length*24};},drawImage(){},fillRect(){},save(){},restore(){},beginPath(){},rect(){},clip(){},translate(){},rotate(){}};contexts.push(ctx);return ctx;
  }})};
  globalThis.Image=class{set src(value){this.url=value;queueMicrotask(()=>this.onload());}};
  globalThis.fetch=async(url)=>({ok:true,json:async()=>JSON.parse(await fs.readFile(new URL(url.split('?')[0],import.meta.url),'utf8'))});
  try{
    const {createLecture}=await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
    const scene=new Three.Scene(),lecture=await createLecture(scene,{capabilities:{getMaxAnisotropy:()=>8}});
    const boards=scene.children.filter(o=>o.name.startsWith('Sliding chalkboard'));
    const trayChalk=scene.children.filter(o=>o.name.startsWith('Tray chalk ')),trayErasers=scene.children.filter(o=>o.name.startsWith('Tray eraser '));
    assert.equal(trayChalk.length,12);assert.equal(trayErasers.length,3);
    for(let column=0;column<3;column++)assert.equal(new Set(trayChalk.filter(o=>o.userData.column===column).map(o=>o.material.color.getHex())).size,4);
    assert.equal(lecture.report.id,'hu');assert.equal(lecture.pages[0].author,'胡勇');assert.equal(lecture.pages.length,32);
    assert.equal(lecture.reportButtons.find(button=>button.userData.selected).userData.reportId,'hu');
    await lecture.setLanguage('en');assert.equal(lecture.language,'en');assert(lecture.copy(0).title.toLowerCase().includes('canonical'));await lecture.setLanguage('zh');
    assert.equal(boards.length,6);assert(!scene.getObjectByName('Six-board lecture wall'));
    const rails=scene.children.filter(o=>o.name.startsWith('Double-channel lift track'));assert.equal(rails.length,3);
    for(let column=0;column<3;column++){
      const [lower,upper]=boards.slice(column*2,column*2+2),bounds=o=>new Three.Box3().setFromObject(o);
      const seam=(bounds(upper).min.y-bounds(lower).max.y)*LECTURE_SCALE;
      assert(seam>.02&&seam<.035,'Resting board-to-board seam is about 3 cm');
      const topGap=(bounds(rails[column].getObjectByName('Upper rail stop')).min.y-bounds(upper).max.y)*LECTURE_SCALE;
      assert(topGap>.04&&topGap<.06,'Upper board clears the top stop by about 5 cm');
      const tray=scene.getObjectByName('Wide nanmu chalk tray '+(column+1));
      const trayGap=(bounds(lower).min.y-bounds(tray).max.y)*LECTURE_SCALE;
      assert(trayGap>.035&&trayGap<.055,'Raised tray sits close below the lower frame without touching');
      assert(Math.abs(tray.userData.floorTop-.655)<1e-9);
      for(let step=0;step<=100;step++){
        const heights=boardHeights(step/100);lower.position.y=heights[0];upper.position.y=heights[1];
        assert(!bounds(lower).intersectsBox(bounds(upper)),'Separate depth channels keep every lift pose collision-free');
        for(const board of [lower,upper]){
          assert(bounds(board).max.y<bounds(rails[column].getObjectByName('Upper rail stop')).min.y);
          assert(bounds(board).min.y>bounds(rails[column].getObjectByName('Lower rail stop')).max.y);
        }
      }
      [lower.position.y,upper.position.y]=boardHeights(0);
    }
    for(const board of boards){
      assert(!board.children.some(o=>o.isMesh&&o.scale.x===.55&&o.scale.y===.05&&o.scale.z===.09),'No redundant pale grab handle below the board');
      const body=board.getObjectByName('Solid opaque board body');assert(body?.isMesh);assert(body.scale.z>.07);
      const face=board.getObjectByName('Matte writing face');
      assert(face.position.z-(body.position.z+body.scale.z/2)>=.009,'Writing face has clearance from its opaque backing');
      assert(face.material.depthTest&&face.material.depthWrite&&!face.material.transparent);
      assert(face.material.polygonOffset&&face.material.polygonOffsetFactor===0&&face.material.polygonOffsetUnits<0,'Depth bias must not grow at grazing angles and occlude the chalk');
      assert.equal(board.children.filter(o=>o.name==='Guide roller').length,4);
      assert.equal(board.children.filter(o=>o.name==='Rail carriage bracket').length,4);
      for(const edge of board.children.filter(o=>o.name==='Thin nanmu frame')){assert.equal(edge.scale.y,.035);assert(edge.material.map.isDataTexture);assert(edge.material.bumpMap);assert.equal(edge.material.color.getHexString(),'735c3e');assert.equal(edge.material.roughness,.65);}
      scene.updateMatrixWorld(true);
      const center=board.getWorldPosition(new Three.Vector3()),ray=new Three.Raycaster(center.clone().add(new Three.Vector3(0,0,-.4)),new Three.Vector3(0,0,1));
      assert(ray.intersectObject(body).length>0,'Rear view hits a solid back rather than vanishing');
    }
    for(const [column,eraser] of trayErasers.entries()){
      const box=new Three.Box3().setFromObject(eraser),tray=scene.getObjectByName('Wide nanmu chalk tray '+(column+1));
      assert.equal(tray.userData.depth,.40);assert(tray.userData.depth>.23&&tray.userData.depth<.56);assert(box.min.y>=tray.userData.floorTop-1e-7);
      assert(box.min.z>tray.userData.centerZ-tray.userData.depth/2+.025&&box.max.z<tray.userData.centerZ+tray.userData.depth/2-.025,'Whole eraser is inside tray lips');
      assert(box.min.z>boards[column*2+1].position.z+.08,'Eraser clears the frontmost moving frame');
      assert(eraser.getObjectByName('Textured layered felt').material.bumpMap);
      assert(eraser.getObjectByName('Rounded palm grip'));
    }
    assert.match(scene.getObjectByName('Smart glass report heading').userData.date,/^\d{4}\.\d{2}\.\d{2}$/);
    const hover=lecture.reportButtons[0];hover.userData.hovered=true;lecture.update(.1);assert(hover.userData.sheen.material.uniforms.strength.value>0);lecture.update(.1,true);assert.equal(hover.userData.sheen.material.uniforms.strength.value,0);hover.userData.hovered=false;assert.equal(new Set(boards.map(b=>b.children[0].material.map.uuid)).size,6);
    for(const board of boards){const m=board.children[0].material;assert.equal(m.emissiveIntensity,0);assert.equal(m.specularIntensity,0);assert.equal(m.roughness,1);assert.equal(m.envMapIntensity,0);}
    assert.deepEqual(lecture.consoleButtons.map(b=>b.userData.action),['language','language','language']);
    const layoutRoot=new Three.Group();configureLectureRoot(layoutRoot);layoutRoot.updateMatrixWorld(true);
    const glassInnerX=(HALL.east-.035/2)*BUILDING_SCALE;
    for(const rail of rails){
      assert(rail.userData.glassMounted);
      const bounds=new Three.Box3().setFromObject(rail).applyMatrix4(layoutRoot.matrixWorld);
      assert(glassInnerX-bounds.max.x>0&&glassInnerX-bounds.max.x<.005,'Mounting pads meet the glass with a tiny non-flickering clearance');
    }
    for(const b of lecture.consoleButtons){const h=layoutRoot.localToWorld(b.position.clone()).y-DECK_Y*BUILDING_SCALE;assert(h>.85&&h<1.1,'Language button sits below the writing boards');}
    const button=lecture.consoleButtons[0],rest=button.position.z;button.userData.pressed=true;lecture.update(.1);assert.equal(button.position.z,rest);assert.equal(button.material.opacity,0);assert(button.userData.smartGlass);button.userData.pressed=false;
    for(const control of [...lecture.consoleButtons,...lecture.reportButtons]){
      control.userData.pressed=true;control.userData.hovered=true;lecture.update(.1);
      assert.equal(control.material.opacity,0);assert.equal(control.material.colorWrite,false,'Clickable hit plane cannot draw a rectangular background');
      control.userData.pressed=false;control.userData.hovered=false;
    }
    lecture.setConsoleState();assert(lecture.consoleButtons[0].userData.lastLabel);
    assert(button.userData.singleToggle);
    for(const [column,control] of lecture.consoleButtons.entries()){
      const touchPosition=layoutRoot.localToWorld(control.position.clone()),halfWidth=control.geometry.parameters.width*.72/2;
      assert.equal(control.position.x,22.4+column*5.6,'Language label centered beneath column');
      const center=22.4+column*5.6;
      assert(Math.abs(control.position.x-center)+control.geometry.parameters.width/2<2.65,'Control stays beneath its own board column');
      assert(touchPosition.y+control.geometry.parameters.height*.72/2<DECK_Y*BUILDING_SCALE+1.23,'Touch control clears the board backing');
    }
    await lecture.setLanguage('en');assert(lecture.consoleButtons.every(b=>b.userData.lastLabel==='en'&&b.userData.visibleLabel==='中'&&b.userData.targetLanguage==='zh'));
    await lecture.setLanguage('zh');assert(lecture.consoleButtons.every(b=>b.userData.lastLabel==='zh'&&b.userData.visibleLabel==='Eng'&&b.userData.targetLanguage==='en'));
    assert.equal(new Set(lecture.consoleButtons.map(b=>b.userData.texture)).size,1,'All controls share the same visible language state');
    const phases=new Set(),eraserStates=new Set(),movingEraser=scene.getObjectByName('Moving blackboard eraser');let returnCompleted=false;
    for(let i=0;i<3500;i++){
      const before=movingEraser.userData.state;lecture.update(.1);phases.add(lecture.clock.phase);eraserStates.add(movingEraser.userData.state);
      assert.equal(trayErasers.filter(o=>o.visible).length+(movingEraser.visible?1:0),3,'One eraser per column, with no duplicate while in use');
      if(movingEraser.visible&&['pickup','returning'].includes(movingEraser.userData.state)){
        const movingBox=new Three.Box3().setFromObject(movingEraser).expandByScalar(-.001);
        for(const board of boards)assert(!movingBox.intersectsBox(new Three.Box3().setFromObject(board.getObjectByName('Solid opaque board body'))),'Eraser transfer clears every board backing');
        for(let c=1;c<=3;c++)for(const part of scene.getObjectByName('Wide nanmu chalk tray '+c).children)assert(!movingBox.intersectsBox(new Three.Box3().setFromObject(part)),'Eraser transfer clears tray floor and all lips');
      }
      if(movingEraser.userData.state==='pickup'){
        assert.equal(lecture.clock.progress,0,'No ink disappears before the eraser arrives');
        const rest=trayErasers[Math.floor(lecture.clock.active/2)];assert(!rest.visible);
        if(before!=='pickup'){
          assert(movingEraser.position.distanceTo(rest.position)<1e-8,'Pick up the eraser exactly where it lies in this column’s tray');
          lecture.playing=false;const position=movingEraser.position.clone();lecture.update(.1);assert(position.distanceTo(movingEraser.position)<1e-8,'Pause also freezes pickup');lecture.playing=true;
        }
      }
      if(before==='returning'&&movingEraser.userData.state==='resting'){
        assert(trayErasers.some(o=>o.position.distanceTo(movingEraser.position)<1e-8&&o.quaternion.angleTo(movingEraser.quaternion)<1e-6),'Return ends exactly on the tray, felt down');returnCompleted=true;
      }
      if(i%10===0)await Promise.resolve();
    }
    assert(eraserStates.has('pickup')&&eraserStates.has('erasing')&&eraserStates.has('returning')&&returnCompleted);
    assert(phases.has('write'));assert(phases.has('erase'));assert(phases.has('lift'));
    assert(scene.getObjectByName('Writing chalk').userData.length<.17);
    assert(scene.getObjectByName('Falling chalk powder').geometry.attributes.position.count===64);
    lecture.playing=false;const time=lecture.clock.elapsed;lecture.update(.1);assert.equal(lecture.clock.elapsed,time);
    const uploads=boards.map(b=>b.children[0].material.map.version);
    for(let i=0;i<50;i++)lecture.update(.1);
    assert.deepEqual(boards.map(b=>b.children[0].material.map.version),uploads,'Unchanged boards must not re-upload textures');
    lecture.lift(0,1);for(let i=0;i<50;i++)lecture.update(.1);
    assert(Math.abs(boards[0].position.y-BOARD_LAYOUT.high)<.001);assert(Math.abs(boards[1].position.y-BOARD_LAYOUT.low)<.001);
    lecture.select(lecture.pages.length-1);await Promise.resolve();lecture.staticPage();lecture.update(.1,true);
    assert.equal(lecture.clock.page,lecture.pages.length-1);assert.equal(lecture.clock.slots[lecture.clock.active].progress,1);
    assert(!scene.getObjectByName('Writing chalk').visible);assert(!scene.getObjectByName('Moving blackboard eraser').visible);
    assert(!scene.getObjectByName('Falling chalk powder').visible);
    assert(boards.every(b=>b.children[0].material.roughnessMap.isCanvasTexture));
    for(const board of boards)assert(board.position.toArray().every(Number.isFinite));
    assert(lecture.focus().toArray().every(Number.isFinite));
    assert.equal(lecture.reportButtons.length,4);
    for(const b of lecture.reportButtons){
      const frameGap=19.4-(b.position.x+b.geometry.parameters.width/2);
      assert(frameGap>.6&&frameGap<.8,'Selector moves slightly left and remains clear of the blackboard frame');
      assert(b.position.x-b.geometry.parameters.width/2>8.4);
    }
    await lecture.setLanguage('en');
    const fetchReport=globalThis.fetch;
    globalThis.fetch=async()=>({ok:false});await assert.rejects(lecture.setReport('duan'));
    assert.equal(lecture.report.id,'hu','Failed loading preserves the current talk');assert.equal(lecture.pendingReport,null);
    let releaseDuan;
    globalThis.fetch=url=>url.includes('/duan/')?new Promise(resolve=>{releaseDuan=()=>resolve(fetchReport(url));}):fetchReport(url);
    const slowDuan=lecture.setReport('duan');
    assert.equal(lecture.pendingReport.id,'duan','Selection acknowledges the click before the network responds');
    assert.equal(lecture.reportButtons.find(b=>b.userData.selected).userData.reportId,'duan');
    await lecture.setReport('ye');assert.equal(lecture.report.id,'ye');
    releaseDuan();assert.equal(await slowDuan,false);assert.equal(lecture.report.id,'ye','A stale response cannot override the latest selection');
    globalThis.fetch=fetchReport;
    for(const id of ['duan','ye','hu','meng']){
      await lecture.setReport(id);assert.equal(lecture.report.id,id);assert.equal(lecture.clock.page,0);assert.equal(lecture.pages[0].kind,'cover');assert.equal(lecture.language,'en');
      assert.equal(lecture.pages.length,id==='meng'?38:id==='hu'?32:26);assert(lecture.clock.slots.every(slot=>slot.page<=0));assert(lecture.reportButtons.find(b=>b.userData.selected).userData.reportId===id);
      assert(trayErasers.every(e=>e.visible));assert(!movingEraser.visible);lecture.update(.1);
      // Once the title is written, allow a brief reading beat before board two.
      const clock=lecture.clock;clock.elapsed=clock.duration-.05;clock.update(.1);
      assert.equal(clock.phase,'hold');assert.equal(clock.slots[clock.active].progress,1);
      for(let i=0;i<19;i++)lecture.update(.1);
      assert.equal(clock.page,0,'Keep a short pause after the final title stroke');
      lecture.playing=false;lecture.update(.1);assert.equal(clock.page,0,'Manual pause remains respected');lecture.playing=true;
      for(let i=0;i<2;i++)lecture.update(.1);
      assert.equal(clock.page,1,'Begin the second board transition about two seconds after the title');
    }
    lecture.select(3);await lecture.setReport('meng');assert.equal(lecture.clock.page,0,'Selecting the current report restarts its title board');
    globalThis.fetch=async()=>{throw new Error('Offline');};await lecture.setReport('hu');assert.equal(lecture.report.id,'hu','A prepared report switches without another network request');assert.equal(lecture.clock.phase,'write','A clean title board starts without an empty lift delay');
    await lecture.seek(17);assert.equal(lecture.clock.phase,'hold');assert.equal(lecture.clock.page,17);
    assert.deepEqual(lecture.clock.slots.map(s=>s.page).sort((a,b)=>a-b),[12,13,14,15,16,17]);
    assert(lecture.clock.slots.every(s=>s.progress===1));
    lecture.heights().forEach((mix,pair)=>boardHeights(mix).forEach((y,side)=>assert.equal(boards[pair*2+side].position.y,y)));
    assert(!movingEraser.visible);assert(trayErasers.every(e=>e.visible));
    await lecture.seek(2);assert.deepEqual(lecture.clock.slots.filter(s=>s.page>=0).map(s=>s.page).sort((a,b)=>a-b),[0,1,2]);
    const oldSeek=lecture.seek(23),newSeek=lecture.seek(4);await Promise.all([oldSeek,newSeek]);assert.equal(lecture.clock.page,4,'Latest scrub wins');
    const finalPage=lecture.pages.length-1;await lecture.seek(finalPage);assert(lecture.clock.ended);lecture.update(.1);assert.equal(lecture.clock.page,finalPage);
    await lecture.seek(1);assert(!lecture.clock.ended);assert.equal(lecture.clock.phase,'hold');
    // Reentry while erasing used to dereference a cleared wet-ink cache.
    await lecture.seek(7);lecture.clock.select(8);lecture.clock.phase='erase';lecture.clock.elapsed=lecture.clock.duration*.4;
    const eraseProgress=lecture.clock.progress;await lecture.setRenderActive(false);await lecture.setRenderActive(true);
    assert(!lecture.status().includes('Cannot'));assert(Math.abs(lecture.clock.progress-eraseProgress)<1e-9);
    lecture.playing=true;for(let i=0;i<600&&lecture.clock.phase!=='write';i++)lecture.update(.1);
    assert.equal(lecture.clock.phase,'write','Resuming an erase must reach fresh chalk writing');
    lecture.dispose();
    globalThis.fetch=fetchReport;
    const {KM_REPORT}=await import('./seminar-catalog.js');
    const kmRoot=new Three.Group(),km=await createLecture(kmRoot,{capabilities:{getMaxAnisotropy:()=>8}},{reports:[KM_REPORT],defaultReport:'km',requireSelection:true});
    km.playing=true;km.update(.1);assert(!km.playing);assert(!km.hasSelection);assert(km.clock.slots.every(s=>s.page===-1),'Entering a seminar never writes before selection');
    assert(km.screenAction('seminar:chapter:1'));assert(km.hoverTargets.some(t=>t.visible&&t.userData.action==='seminar:section:1.1'));
    assert(!km.hasSelection,'Opening a chapter folder does not start a talk');
    const part=km.navigation.sections[0];await km.setRange(part.start,part.end);km.playing=true;
    assert(km.hasSelection);assert.equal(km.progress.total,part.total);assert.equal(km.clock.active,0);
    await km.setRenderActive(false);assert(kmRoot.visible,'Offscreen scheduling must never hide the board hardware or its last texture');
    assert(kmRoot.children.filter(o=>o.name.startsWith('Sliding chalkboard')).every(b=>b.visible&&b.getObjectByName('Matte writing face').visible));
    let requests=0;globalThis.fetch=async(...args)=>{requests++;return fetchReport(...args);};
    const imagesBefore=contexts.length,versions=kmRoot.children.filter(o=>o.name.startsWith('Sliding chalkboard')).map(b=>b.children[0].material.map.version);
    km.update(30);assert.equal(requests,0);assert.equal(contexts.length,imagesBefore,'Offscreen progress must not allocate/rasterize canvas pages');
    assert.deepEqual(kmRoot.children.filter(o=>o.name.startsWith('Sliding chalkboard')).map(b=>b.children[0].material.map.version),versions,'No offscreen texture uploads');
    assert(km.clock.page>part.start);const progressBefore={page:km.clock.page,progress:km.clock.progress,phase:km.clock.phase};
    const reentry=km.setRenderActive(true);assert(kmRoot.visible,'Boards remain visible while current pages load');await reentry;assert(kmRoot.visible);assert.equal(km.clock.page,progressBefore.page);assert.equal(km.clock.phase,progressBefore.phase);assert(Math.abs(km.clock.progress-progressBefore.progress)<1e-9,'Reentry preserves estimated partial progress');
    const next=km.navigation.sections[1];await km.setRange(next.start,next.end);assert.equal(km.clock.active,0);assert(km.clock.slots.filter(s=>s.page>=0).every(s=>s.page===next.start),'A new student starts on clean boards');
    await km.seek(next.end);for(let i=0;i<100;i++)km.update(.1);assert.equal(km.clock.page,next.end);assert(km.clock.ended);km.dispose();
    let forbiddenFetch=0;globalThis.fetch=async()=>{forbiddenFetch++;throw Error('Disabled room fetched content');};
    const emptyRoot=new Three.Group(),empty=await createLecture(emptyRoot,{capabilities:{getMaxAnisotropy:()=>8}}, {disabled:true});
    assert.equal(forbiddenFetch,0);assert.equal(emptyRoot.children.filter(o=>o.name.startsWith('Sliding chalkboard')).length,6);
    assert.equal(await empty.setReport('hu'),false);assert.equal(await empty.setRange(0,3),false);empty.playing=true;empty.staticPage();empty.update(30);
    assert(!empty.playing);assert(!empty.hasSelection);assert(empty.clock.slots.every(s=>s.page===-1));assert.equal(empty.hoverTargets.length,0);empty.dispose();
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
  const lecture={pages,clock:{page:0},playing:true,report:{id:'meng'}};
  const source=(await fs.readFile(new URL('./chalk-reader.js',import.meta.url),'utf8')).replace('./chalk-typography.js?v62-chalk-ink',new URL('./chalk-typography.js',import.meta.url).href).replace('./control-label.js?v=22-handwritten-cover',new URL('./control-label.js',import.meta.url).href).replace('./display-profile.js?v=8-cover',new URL('./display-profile.js',import.meta.url).href);
  try{
    const {createChalkReader}=await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
    const reader=createChalkReader(lecture),panel=elements.get('chalkReader');
    reader.chapter(true);assert(!panel.hidden);assert(elements.get('readerFormula').src.includes('formula-001.svg'));assert.equal(elements.get('readerExplanation').textContent,pages[0].text);
    elements.get('readerClose').click();reader.chapter(true);assert(panel.hidden,'Do not reopen dismissed reader on same chapter');
    reader.chapter(false);reader.chapter(true,false);assert(panel.hidden,'Do not cover the manually opened board control panel');
    elements.get('readerOpen').click();assert(!panel.hidden);
    elements.get('readerFont').value='30';elements.get('readerFont').events.input();assert.equal(elements.get('readerFormula').style.width,readingFormulaWidth(pages[0].formulaEm,30)+'px');
    lecture.clock.page=1;reader.update();assert.equal(elements.get('readerExplanation').textContent,pages[1].text);
    lecture.pages=JSON.parse(await fs.readFile(new URL('./assets/chalk/hu/pages.json',import.meta.url),'utf8')).pages;lecture.report={id:'hu'};reader.update();assert.equal(elements.get('readerTitle').textContent,lecture.pages[1].title,'Reader refreshes at the same page number after switching talks');
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
  const app=await fs.readFile(new URL('./app.js?v=43-tight-boards',import.meta.url),'utf8');
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
  const source=await fs.readFile(new URL('./app.js?v=43-tight-boards',import.meta.url),'utf8');
  const resume=source.slice(source.indexOf('function beginTransition'),source.indexOf('function applyShot'));
  assert(resume.includes('camera.position.clone()')&&resume.includes('controls.target.clone()'));
  assert(resume.includes('controls.enableDamping=false')&&resume.includes('beginTransition();updateLabels()'));
  const apply=source.slice(source.indexOf('function applyShot'),source.indexOf('function resize'));
  assert(apply.includes('motionCoordinate('));assert(apply.includes('slerpQuaternions('));
  assert(!apply.includes('Math.sin(k*Math.PI)'));
  assert(!source.includes('fadeAt('));assert(source.includes('stamp-opening.started>=OPENING_OVERVIEW_MS'));assert(source.includes('const index=Number(button.dataset.shot)'));assert(source.includes('selectShot(index)'));assert(source.includes('else if(blend)'));
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

test('camera retargeting preserves velocity and acceleration and settles without a snap',async()=>{
  const {motionCoordinate}=await import('./camera-motion.js');
  for(const [start,end,velocity,acceleration,duration] of [[0,100,0,0,9],[20,-15,4,-.2,8],[-12,30,-2,.15,12]]){
    const h=.0001,position=t=>motionCoordinate(start,end,velocity,acceleration,duration,t/duration);
    assert.equal(position(0),start);assert(Math.abs(position(duration)-end)<1e-8);
    assert(Math.abs((position(h)-position(0))/h-velocity)<.001);
    assert(Math.abs((position(2*h)-2*position(h)+position(0))/(h*h)-acceleration)<.01);
    assert(Math.abs((position(duration)-position(duration-h))/h)<.001);
    assert(Math.abs((position(duration)-2*position(duration-h)+position(duration-2*h))/(h*h))<.01);
  }
  const desktop=displayProfile(1440,900,2,'high',4,4);
  assert(desktop.direct&&desktop.samples===4,'Native desktop antialiasing does not need another full-screen render pass');
  assert(!displayProfile(1440,900,2,'high',4,0).direct,'Keep the compositor fallback without native MSAA');
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
  for(const text of ['FᵖHⁿ','d²=0','Eᵣ','∂∂̄','𝓕','(−1)ᵖ','α→β']){
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
 for(const p of pages)for(const c of p.source+p.title+(p.author||'')+p.text)if(/[\u3400-\u9fff]/.test(c))assert(coverage.characters.includes(c),'Missing handwritten character '+c);
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


test('English prose remains handwritten while embedded mathematical variables stay print',async()=>{
  const {chalkRuns,chalkHTML}=await import('./chalk-typography.js');
  for(const text of ['Spectral Sequences','Sheng Meng','A double complex','Kähler and Dolbeault cohomology','Take the image of the map.']){
    assert(chalkRuns(text).every(run=>!run.math),text);
    assert(!chalkHTML(text).includes('chalk-math'),text);
  }
  const runs=chalkRuns('Let K be a double complex. The total differential D preserves the filtration.');
  assert.deepEqual(runs.filter(run=>run.math).map(run=>run.text),['K','D']);
  const calls=[],ctx={clearRect(){},fillText(text){calls.push({text,font:this.font});},measureText(t){return {width:[...t].length*20};},drawImage(){throw Error('The cover must not draw a formula');}};
  const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/pages.json',import.meta.url),'utf8'));
  assert.equal(pages[0].kind,'cover');assert.equal(pages[0].author,'孟晟');assert.equal(pages[1].source,'§ 1.1–1.5');assert.equal(pages[1].diagram.kind,'double');
  composeChalkPage(ctx,pages[0],0,'zh',null);
  assert(calls.some(c=>c.text==='孟晟'&&c.font.includes('RefugeChinese')));
  composeChalkPage(ctx,pages[0],0,'en',null);
  assert(calls.some(c=>c.text==='Spectral Sequences'&&c.font.includes('RefugeLatin')));
  assert(calls.some(c=>c.text==='Sheng Meng'&&c.font.includes('RefugeLatin')));
});

test('speaker reports preserve paper sources, hypotheses, bilingual covers and complete assets',async()=>{
  const {REPORTS}=await import('./report-catalog.js');
  assert.deepEqual(REPORTS.map(r=>r.speaker),['胡勇','段治豪','叶东','孟晟']);
  const coverage=JSON.parse(await fs.readFile(new URL('./assets/fonts/chalk-coverage.json',import.meta.url),'utf8'));
  for(const report of REPORTS.filter(report=>report.id!=='meng')){
    const data=JSON.parse(await fs.readFile(new URL(report.manifest,import.meta.url),'utf8'));
    assert.equal(data.source,report.url);assert.deepEqual(data.authors,report.authors);assert.equal(data.license,report.license||'CC BY 4.0');
    assert.equal(data.pages.length,report.id==='hu'?32:26);assert.equal(data.pages.filter(p=>!p.kind).length,report.id==='hu'?30:24);assert.equal(data.pages.at(-1).kind,'closing');assert.equal(data.pages.at(-1).title,'谢谢！');assert.equal(data.pages[0].author,report.speaker);assert.equal(data.pages[0].en.author,report.speakerEn);
    for(const page of data.pages){
      for(const c of page.source+page.title+page.text+(page.author||''))if(/[\u3400-\u9fff]/.test(c))assert(coverage.characters.includes(c),`Missing glyph ${c}`);
      assert(page.en.title&&(page.en.text||page.kind==='closing'));assert(!/[\u3400-\u9fff]/.test(page.en.source));
      for(const path of [page.asset,page.formulaAsset]){const svg=await fs.readFile(new URL(path,import.meta.url),'utf8');assert(svg.startsWith('<svg'));assert(!svg.includes('data-mjx-error'));}
    }
    if(report.id==='hu'){assert(data.pages.find(p=>p.title==='新的几何亏格门槛').tex.includes('243'));assert(data.pages.find(p=>p.title==='等号要求怎样的纤维').text.includes('243'));assert(data.pages.find(p=>p.title==='高次数迫使纤维正则').tex.includes('243'));assert(data.pages.some(p=>p.diagram?.kind==='canonical'));}
    if(report.id==='ye')assert(data.pages.find(p=>p.source==='定理 1.1').tex.includes('fixed'));
  }
});

test('inline p_g uses a real printed subscript in canvas, reader and SVG',async()=>{
  const {chalkInlineRuns,chalkHTML,chalkSVG}=await import('./chalk-typography.js');
  assert.deepEqual(chalkInlineRuns('p_g(X)'),[{text:'p',math:true},{text:'g',math:true,script:'sub'},{text:'(X)',math:true}]);
  assert(chalkHTML('p_g(X)').includes('<sub>g</sub>'));assert(!chalkHTML('p_g(X)').includes('_'));
  assert(chalkSVG('p_g(X)').includes('baseline-shift="sub"'));
  assert(chalkHTML('K_X^2').includes('<sup>2</sup>'));
  const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/hu/pages.json',import.meta.url),'utf8'));
  for(const language of ['zh','en']){
    const calls=[],ctx={clearRect(){},drawImage(){},fillText(text,x,y){calls.push({text,x,y,font:this.font});},measureText(text){return {width:text.length*parseFloat(this.font)*.5};}};
    const rows=composeChalkPage(ctx,pages.find(p=>p.title==='等号要求怎样的纤维'),0,language,{}),p=calls.find(c=>c.text==='p'),g=calls.find(c=>c.text==='g');
    assert(p&&g);assert(g.y>p.y);assert(parseFloat(g.font)<parseFloat(p.font));assert(g.font.includes('RefugeMath'));assert(!calls.some(c=>c.text.includes('p_g')));
    assert(rows.some(([x,y,w,h])=>g.x>=x&&g.x<x+w&&g.y>y&&g.y+parseFloat(g.font)*.25<y+h),'Reveal bounds include the subscript descender');
  }
});

test('handwritten descenders and script offsets fit the actual ink reveal bounds',()=>{
  const calls=[];
  const metrics=(text,font)=>{const px=parseFloat(font);return {width:text.length*px*.44,actualBoundingBoxLeft:px*.09,actualBoundingBoxRight:text.length*px*.44+px*.07,actualBoundingBoxAscent:px*.76,actualBoundingBoxDescent:/[gpqy]/.test(text)?px*.43:px*.06};};
  const ctx={clearRect(){},drawImage(){},measureText(text){return metrics(text,this.font);},fillText(text,x,y){calls.push({x,y,...metrics(text,this.font)});}};
  const page={kind:'cover',en:{title:'Geometry',author:'Yong Hu',text:'Study p_g(X)'},title:'Geometry',author:'Yong Hu',text:'Study p_g(X)'};
  const rows=composeChalkPage(ctx,page,0,'en',null);
  for(const ink of calls)assert(rows.some(([x,y,w,h])=>x<=ink.x-ink.actualBoundingBoxLeft&&y<=ink.y-ink.actualBoundingBoxAscent&&x+w>=ink.x+ink.actualBoundingBoxRight&&y+h>=ink.y+ink.actualBoundingBoxDescent),'The mask must include real descenders and overhanging strokes, not a fixed extra 10 pixels');
});

test('the final thanks board remains complete without automatically restarting',()=>{
  const clock=new LectureClock(3);clock.select(2);clock.setDurations(2,{write:.2});clock.startWrite();
  for(let i=0;i<10;i++)clock.update(.1);
  assert(clock.ended);assert.equal(clock.page,2);assert.equal(clock.phase,'hold');assert.equal(clock.slots[clock.active].progress,1);
  const elapsed=clock.elapsed;for(let i=0;i<12000;i++)clock.update(.1);
  assert.equal(clock.page,2);assert.equal(clock.elapsed,elapsed);clock.next();assert(clock.ended);
  clock.next(-1);assert.equal(clock.page,1);assert(!clock.ended);
});


test('all report reveal rectangles isolate later lines, including inline scripts',async()=>{
  const ctx={clearRect(){},fillText(){},drawImage(){},measureText(t){return {width:[...t].length*parseFloat(this.font)*.65};}};
  for(const file of ['pages.json','hu/pages.json','ye/pages.json','duan/pages.json']){
    const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/'+file,import.meta.url),'utf8'));
    for(const page of pages)for(const lang of ['zh','en']){
      const rows=composeChalkPage(ctx,page,0,lang,{});
      for(let i=0;i<rows.length;i++)for(let j=i+1;j<rows.length;j++){
        // Paths are drawn separately after the text; their bounds are not scan clips.
        if(rows[i].strokePath||rows[j].strokePath)continue;
        const [x,y,w,h]=rows[i],[a,b,c,d]=rows[j];
        assert(x+w<=a||a+c<=x||y+h<=b||b+d<=y,`${file} ${page.title} ${lang}: reveal rows ${i}/${j} overlap`);
      }
    }
  }
});
test('automatic glass doors open on hover and close only after a stable delay',async()=>{
  const {createAutomaticDoors}=await import('./automatic-doors.js');
  const system=createAutomaticDoors(Three,new Three.MeshBasicMaterial(),new Three.MeshBasicMaterial()),root=new Three.Group();
  const group=system.add(root,{x:0,y:0,z:0,width:2,height:2,axis:'x',name:'test'});
  const sensor=system.targets[0],sensorPosition=sensor.position.clone();
  sensor.userData.hovered=true;for(let i=0;i<30;i++)system.update(.1);
  assert(sensor.userData.opening>.9999);assert(sensorPosition.equals(sensor.position),'Fixed sensor cannot escape the pointer as leaves open');
  assert(group.children[0].position.x< -1.5&&group.children[1].position.x>1.5);
  sensor.userData.hovered=false;for(let i=0;i<10;i++)system.update(.1);assert(sensor.userData.opening>.99);
  for(let i=0;i<50;i++)system.update(.1);assert(sensor.userData.opening<.001);system.dispose();
});
test('hover lights text without activating controls and cancels cleanly',()=>{
  const events={},canvas={style:{cursor:'crosshair'},addEventListener(t,f){events[t]=f;},removeEventListener(t){delete events[t];}};
  const target={userData:{action:'language'}},controls={enabled:true};let actions=0;
  const binding=bindPhysicalButtons(canvas,controls,()=>target,()=>actions++);
  events.pointermove({buttons:0});assert(target.userData.hovered);assert.equal(actions,0);assert.equal(canvas.style.cursor,'pointer');
  events.pointerleave();assert(!target.userData.hovered);assert.equal(canvas.style.cursor,'crosshair');binding.dispose();assert.deepEqual(events,{});
});
test('date heading follows Shanghai midnight and upper rails cover all but stated openings',async()=>{
  const {seminarDate}=await import('./smart-screen.js'),{perimeterRails}=await import('./upper-guards.js');
  assert.equal(seminarDate(new Date('2026-09-22T16:01:00Z')),'2026.09.23');
  const rectangles=[[0,10,0,8],[-2,2,3,5]],openings=[{axis:'x',fixed:5,from:-1.8,to:-.6}],segments=perimeterRails(rectangles,openings);
  const length=edges=>edges.reduce((sum,[a,b,c,d])=>sum+Math.hypot(c-a,d-b),0);
  assert(Math.abs(length(platformUnion(rectangles).edges)-length(segments)-1.2)<1e-8);
});
