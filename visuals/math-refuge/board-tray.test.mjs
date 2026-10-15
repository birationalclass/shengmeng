import test from 'node:test';import assert from 'node:assert/strict';
import * as T from '../3d/vendor/three.module.js';
import {createBoardTrayHardware} from './board-tray.js';
import {TRAY_DOCK,trayControlLayout,placeTrayControl} from './board-tray-layout.js';
import {BOARD_SHAFT} from './site-layout.js';
import {createBoardPageControls} from './board-page-control.js';
import {createBoardCameraControl} from './board-camera-control.js';
import {createBoardVoicePanel} from './report-voice.js';
import {updateTextSheen} from './smart-screen.js';
import {createBoardHardware,TRAY} from './board-hardware.js';
import {ERASER_HALF_WIDTH,ERASER_HALF_HEIGHT} from './chalk-motion.js';
test('concept eraser is one rounded wood cap with the exact original felt contact and tray rest height',()=>{
 const hardware=createBoardHardware(T),trayHardware=createBoardTrayHardware(T),scene=new T.Scene(),w=ERASER_HALF_WIDTH*2/1536*5.3,h=ERASER_HALF_HEIGHT*2/640*2.05,eraser=trayHardware.createEraser(w,h,hardware),tray=trayHardware.create(scene,0,0);scene.add(eraser);
 try{assert.equal(eraser.children.length,1,'single cap with a thin dark felt base, no raised grip or grooves');assert.equal(eraser.material,tray.children[0].material);const felt=eraser.getObjectByName('Textured layered felt'),feltBounds=new T.Box3().setFromObject(felt);assert(Math.abs(feltBounds.min.z+.065)<1e-8);assert.equal(felt.material,hardware.felt);assert([...eraser.geometry.getAttribute('uv').array].every(Number.isFinite));
 const rest=eraser.clone();rest.position.set(0,TRAY.restY,TRAY.z);rest.rotation.set(-Math.PI/2,0,.035);const box=new T.Box3().setFromObject(rest);assert(Math.abs(box.min.y-TRAY.top)<1e-7,'felt sits on the gutter floor without floating');assert(box.max.y-box.min.y<.10);assert(box.min.z>TRAY.z-TRAY.depth/2&&box.max.z<TRAY.z+TRAY.depth/2);trayHardware.setTone('deep');assert.equal(eraser.material.map,tray.children[0].material.map);trayHardware.setTone('pale');assert.notEqual(eraser.material.map,felt.material.map);assert.equal(eraser.material.map,tray.children[0].material.map);
 }finally{trayHardware.dispose();hardware.dispose();}
});
test('all tone options recolor board frames and tray together, and gradient follows height',()=>{
 const hardware=createBoardTrayHardware(T),scene=new T.Scene(),tray=hardware.create(scene,0,0),frame=hardware.createFrame(scene,5.3,2.05),wood=tray.children[0].material;
 try{assert.equal(hardware.tone,'pale','the approved pale finish is the default');for(const tone of ['pale','deep','honey','gradient']){assert.equal(hardware.setTone(tone),tone);assert.equal(frame.children[0].material,wood);assert(frame.children.every(r=>r.geometry.getAttribute('color')));assert(tray.children[0].geometry.getAttribute('color'));}
 const top=frame.children[0].geometry.getAttribute('color'),bottom=frame.children[1].geometry.getAttribute('color');assert(top.getX(0)>bottom.getX(0),'top rail is lighter than bottom rail');hardware.setTone('deep');assert.equal(wood.color.getHexString(),'646464');assert.equal(frame.children[0].geometry.getAttribute('color').getX(0),1);
 }finally{hardware.dispose();}
});
test('pale finish has its own shared albedo and switching finishes does not decode textures again',async()=>{
 const loaded=[];let disposed=0;const Fake={...T,TextureLoader:class{async loadAsync(src){const map=new T.Texture();map.userData.source=src;map.addEventListener('dispose',()=>disposed++);loaded.push(map);return map;}}},hardware=createBoardTrayHardware(Fake),scene=new T.Scene(),tray=hardware.create(scene,0,0),frame=hardware.createFrame(scene,5.3,2.05),wood=tray.children[0].material;
 try{await hardware.loadGrain();const pale=wood.map;assert.equal(loaded.length,2);assert.equal(frame.children[0].material.map,pale);assert(pale.userData.source.startsWith('data:image/jpeg;base64,'));hardware.setTone('deep');assert.notEqual(wood.map,pale);hardware.setTone('pale');assert.equal(wood.map,pale);assert.equal(wood.bumpMap,pale);assert(wood.roughness>=.7);assert.equal(loaded.length,2,'reuse both decoded maps across the six frames and three trays');}finally{hardware.dispose();}assert.equal(disposed,2);
});
test('mitered board frame shares the tray wood and leaves the entire writing face unobstructed',()=>{
 const hardware=createBoardTrayHardware(T),scene=new T.Scene(),tray=hardware.create(scene,0,0),board=new T.Group();scene.add(board);const frame=hardware.createFrame(board,5.3,2.05),second=hardware.createFrame(new T.Group(),5.3,2.05);
 try{assert.equal(frame.children.length,4);assert.equal(frame.children[0].material,tray.children[0].material);assert.equal(second.children[0].geometry,frame.children[0].geometry,'six boards reuse the same beveled rails');scene.updateMatrixWorld(true);
 for(const x of [-2.65,0,2.65])for(const y of [-1.025,0,1.025])assert.equal(new T.Raycaster(new T.Vector3(x,y,2),new T.Vector3(0,0,-1)).intersectObjects(frame.children).length,0,'no wood covers even the edge of the writing plane');
 const box=new T.Box3().setFromObject(frame);assert(box.max.z-box.min.z<.08);assert(box.max.x<2.70);assert(box.max.y<1.075);for(const rail of frame.children)assert([...rail.geometry.getAttribute('uv').array].every(Number.isFinite));
 }finally{hardware.dispose();}
});
test('tray hover and held press are visible without moving or shrinking the physical target',()=>{
 const mesh=new T.Mesh(new T.PlaneGeometry(.6,.6),new T.MeshBasicMaterial()),p=trayControlLayout().next;mesh.userData={action:'board:next',smartGlass:true};placeTrayControl(mesh,p);const scale=mesh.scale.clone();
 mesh.userData.hovered=true;updateTextSheen(T,mesh,.1,false);assert(mesh.userData.trayFeedback.uniforms.strength.value>0);mesh.userData.pressed=true;for(let i=0;i<8;i++)updateTextSheen(T,mesh,.1,false);assert(mesh.scale.equals(scale),'pointerup near a target edge must still hit');assert.equal(mesh.userData.trayFeedback.uniforms.strength.value,.8);mesh.userData.hovered=mesh.userData.pressed=false;updateTextSheen(T,mesh,.1,false);assert.equal(mesh.userData.trayFeedback.uniforms.strength.value,0);mesh.material.dispose();mesh.geometry.dispose();
});
test('rounded tray and inclined glass fit the retraction shaft, with valid fine-grain UVs',()=>{
 const hardware=createBoardTrayHardware(T,8),scene=new T.Scene();
 try{for(let column=0;column<3;column++){
  const group=hardware.create(scene,22.4+5.6*column,column),box=new T.Box3().setFromObject(group);
  assert(box.min.x>BOARD_SHAFT.left&&box.max.x<BOARD_SHAFT.right);assert(box.min.z>BOARD_SHAFT.back&&box.max.z<BOARD_SHAFT.front);
  assert.equal(group.children.filter(m=>m.name.includes('Continuous')).length,1,'one continuous shell, without overlapping end plates');
  for(const mesh of group.children){assert([...mesh.geometry.getAttribute('position').array].every(Number.isFinite));const uv=mesh.geometry.getAttribute('uv');assert([...uv.array].every(Number.isFinite));}
  const panel=group.children.find(m=>m.name.includes('glass'));assert.equal(panel.rotation.x,-TRAY_DOCK.tilt);assert(panel.material.roughness>.4);
  assert(box.max.y-box.min.y<.24,'the tray remains a slim rail including its concealed supports');
  scene.updateMatrixWorld(true);
  for(const x of [-2,0,2])for(const y of [-.04,0,.04]){const point=panel.localToWorld(new T.Vector3(x,y,.008)),normal=new T.Vector3(0,0,1).transformDirection(panel.matrixWorld),ray=new T.Raycaster(point.clone().add(normal),normal.clone().negate());assert.equal(ray.intersectObjects(group.children,true)[0]?.object,panel,'glass must be visibly in front of the beveled wood, not buried inside it');}
 }}finally{hardware.dispose();}
});
test('all inclined controls can be clicked in front of the real glass and tray, without intercepting neighbours',()=>{
 const old=globalThis.document;globalThis.document={createElement:()=>({getContext:()=>new Proxy({},{get:()=>()=>{},set:()=>true})})};
 const hardware=createBoardTrayHardware(T),scene=new T.Scene(),panels=[];
 try{for(let column=0;column<3;column++){
  hardware.create(scene,22.4+5.6*column,column);
  const pages=createBoardPageControls(T,scene,column);pages.update({previousEnabled:true,nextEnabled:true,visible:true});panels.push(pages);
  const camera=createBoardCameraControl(T,scene,column);camera.update(true,true,true,.5);panels.push(camera);
  const voice=createBoardVoicePanel(T,scene);voice.setColumn(column);voice.mesh.visible=true;panels.push(voice);
  const language=new T.Mesh(new T.PlaneGeometry(1.1,.65),new T.MeshBasicMaterial());language.userData.action='language';placeTrayControl(language,trayControlLayout(column).language);scene.add(language);
  scene.updateMatrixWorld(true);
  for(const [key,action] of Object.entries({language:'language',previous:'board:previous',voice:'voice:toggle',next:'board:next',camera:'camera:toggle',zoomOut:'camera:farther',zoomIn:'camera:closer',reveal:'board:reveal'})){
   const p=trayControlLayout(column)[key],normal=new T.Vector3(0,Math.sin(p.tilt),Math.cos(p.tilt)),center=new T.Vector3(p.x,p.y,p.z),ray=new T.Raycaster(center.clone().add(normal),normal.clone().negate());
   const hit=ray.intersectObjects(scene.children,true)[0];assert.equal(hit?.object.userData.action,action,'visible '+key+' is the first physical hit');
  }
 }}finally{panels.forEach(p=>p.dispose());hardware.dispose();globalThis.document=old;}
});
