import test from 'node:test';
import assert from 'node:assert/strict';
import {OPENING_POSE,OpeningCameraLock} from './opening-camera.js';
import {toBeach} from './elliptic-site.js';
test('opening begins over left ring’s western approach and looks east and downward',()=>{
 const p=toBeach(OPENING_POSE.position[0],OPENING_POSE.position[2]);assert(Math.abs(p[0]+1000)<1e-8&&Math.abs(p[1])<1e-8);
 assert(OPENING_POSE.target[0]>OPENING_POSE.position[0]);
 assert(OPENING_POSE.target[1]<OPENING_POSE.position[1]);
 assert.equal(OPENING_POSE.target[2],OPENING_POSE.position[2]);
});
test('camera lock expires exactly ten seconds after entry',()=>{
 const lock=new OpeningCameraLock();assert(!lock.locked(100));lock.start(100);
 assert.equal(lock.remaining(100),10);assert(lock.locked(10099));assert(!lock.locked(10100));assert.equal(lock.remaining(99999),0);
});

test('keyboard movement uses Q/E for strafe and Space/X for height',async()=>{
 const {KeyboardMotion}=await import('./keyboard-motion.js');
 for(const [key,axis,sign] of [['q','right',-1],['e','right',1],[' ','up',1],['x','up',-1]]){
  const m=new KeyboardMotion(),v=m.update(new Set([key]),.1);assert(v[axis]*sign>0);
 }
});
import {PerspectiveCamera,Vector3} from '../3d/vendor/three.module.js';
import {openingFrameFov} from './opening-camera.js';
test('handoff camera projection matches the poster cover crop on wide and tall screens',()=>{
 const reference=new PerspectiveCamera(OPENING_POSE.fov,1280/720,.1,30000);reference.position.fromArray(OPENING_POSE.position);reference.lookAt(...OPENING_POSE.target);reference.updateMatrixWorld();
 for(const [width,height] of [[1280,720],[2188,1244],[2400,900],[390,844]]){
  const live=new PerspectiveCamera(openingFrameFov(width/height),width/height,.1,30000);live.position.copy(reference.position);live.quaternion.copy(reference.quaternion);live.updateMatrixWorld();
  const scale=Math.max(width/1280,height/720);
  for(const z of [-500,0,500]){
   const point=new Vector3(OPENING_POSE.target[0]+1200,0,z),a=point.clone().project(reference),b=point.clone().project(live);
   const posterX=(a.x+1)*640*scale-(1280*scale-width)/2,posterY=(1-a.y)*360*scale-(720*scale-height)/2;
   assert(Math.abs(posterX-(b.x+1)*width/2)<1e-6);assert(Math.abs(posterY-(1-b.y)*height/2)<1e-6);
  }
 }
});
