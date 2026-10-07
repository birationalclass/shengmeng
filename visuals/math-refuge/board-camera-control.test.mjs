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