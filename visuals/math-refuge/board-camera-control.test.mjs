import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../3d/vendor/three.module.js';
import {createBoardCameraControl} from './board-camera-control.js';
import {reportControlLayout} from './report-voice.js';
test('each camera control has a separate real raycast target and synchronized on/off appearance',()=>{
 const old=globalThis.document;globalThis.document={createElement:()=>({getContext:()=>new Proxy({},{get:()=>()=>{},set:()=>true})})};
 const scene=new T.Scene(),panels=[];
 try{
  for(let column=0;column<3;column++){
   const panel=createBoardCameraControl(T,scene,column);panels.push(panel);panel.update(true,true);scene.updateMatrixWorld(true);
   const position=reportControlLayout(column).camera;
   const ray=new T.Raycaster(new T.Vector3(position.x,position.y,0),new T.Vector3(0,0,-1));
   assert.equal(ray.intersectObjects(scene.children,false)[0].object,panel.mesh,'click reaches the intended column');
   assert.equal(panel.mesh.userData.action,'camera:toggle');assert(panel.mesh.userData.active);assert.match(panel.mesh.userData.label,/开启/);
   panel.update(false,true);assert(!panel.mesh.userData.active);assert.match(panel.mesh.userData.label,/关闭/);
   const playback=reportControlLayout(column).voice;ray.set(new T.Vector3(playback.x,playback.y,0),new T.Vector3(0,0,-1));assert.equal(ray.intersectObject(panel.mesh).length,0,'play click cannot hit camera button');
   panel.update(false,false);assert(!panel.mesh.visible);
  }
 }finally{panels.forEach(p=>p.dispose());globalThis.document=old;}
 assert.equal(scene.children.length,0);
});
test('plus and minus have independent, non-overlapping raycast targets in every column',()=>{
 const old=globalThis.document;globalThis.document={createElement:()=>({getContext:()=>new Proxy({},{get:()=>()=>{},set:()=>true})})};
 const scene=new T.Scene(),panels=[];
 try{for(let column=0;column<3;column++){
  const panel=createBoardCameraControl(T,scene,column);panels.push(panel);panel.update(true,true,true,0);scene.updateMatrixWorld(true);
  assert.equal(panel.meshes.length,3);
  for(const [key,action] of [['zoomOut','camera:farther'],['zoomIn','camera:closer']]){
   const p=reportControlLayout(column)[key],ray=new T.Raycaster(new T.Vector3(p.x,p.y,0),new T.Vector3(0,0,-1));
   const hits=ray.intersectObjects(scene.children,false);assert.equal(new Set(hits.map(h=>h.object)).size,1);assert.equal(hits[0].object.userData.action,action);
  }
  assert(panel.meshes[2].userData.limit);assert(!panel.meshes[1].userData.limit);panel.update(true,true,true,1);assert(panel.meshes[1].userData.limit);assert(!panel.meshes[2].userData.limit);
  panel.update(true,false);assert(panel.meshes.every(m=>!m.visible));
 }}finally{panels.forEach(p=>p.dispose());globalThis.document=old;}assert.equal(scene.children.length,0);
});
