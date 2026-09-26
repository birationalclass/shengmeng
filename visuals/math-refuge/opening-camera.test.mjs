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
