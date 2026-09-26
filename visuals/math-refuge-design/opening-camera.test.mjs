import test from 'node:test';
import assert from 'node:assert/strict';
import {OPENING_POSE,OpeningCameraLock} from './opening-camera.js';
import {toBeach} from './elliptic-site.js';
test('opening begins over left ring’s western approach and looks east and downward',()=>{
 assert.deepEqual(toBeach(OPENING_POSE.position[0],OPENING_POSE.position[2]),[-1000,0]);
 assert(OPENING_POSE.target[0]>OPENING_POSE.position[0]);
 assert(OPENING_POSE.target[1]<OPENING_POSE.position[1]);
 assert.equal(OPENING_POSE.target[2],OPENING_POSE.position[2]);
});
test('camera lock expires exactly fifteen seconds after entry',()=>{
 const lock=new OpeningCameraLock();assert(!lock.locked(100));lock.start(100);
 assert.equal(lock.remaining(100),15);assert(lock.locked(15099));assert(!lock.locked(15100));assert.equal(lock.remaining(99999),0);
});

test('keyboard movement uses Q/E for strafe and Space/X for height',async()=>{
 const fs=await import('node:fs/promises'),vm=await import('node:vm'),T=await import('../3d/vendor/three.module.js');
 const app=await fs.readFile(new URL('./app.js',import.meta.url),'utf8');
 const body=app.slice(app.indexOf("    if(keys.has('w')"),app.indexOf('    if(move.lengthSq())'));
 for(const [key,expected] of [['q',[-1,0,0]],['e',[1,0,0]],[' ',[0,1,0]],['x',[0,-1,0]]]){
  const move=new T.Vector3();vm.runInNewContext(body,{keys:new Set([key]),move,forward:new T.Vector3(0,0,-1),right:new T.Vector3(1,0,0),dt:0});assert.deepEqual(move.toArray(),expected);
 }
});
