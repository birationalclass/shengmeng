import test from 'node:test';
import assert from 'node:assert/strict';
import {OPENING_POSE,OpeningCameraLock} from './opening-camera.js';
import {toBeach} from './elliptic-site.js';
test('opening begins over left ring and looks east and downward',()=>{
 assert.deepEqual(toBeach(OPENING_POSE.position[0],OPENING_POSE.position[2]),[0,0]);
 assert(OPENING_POSE.target[0]>OPENING_POSE.position[0]);
 assert(OPENING_POSE.target[1]<OPENING_POSE.position[1]);
 assert.equal(OPENING_POSE.target[2],OPENING_POSE.position[2]);
});
test('camera lock expires exactly thirty seconds after entry',()=>{
 const lock=new OpeningCameraLock();assert(!lock.locked(100));lock.start(100);
 assert.equal(lock.remaining(100),30);assert(lock.locked(30099));assert(!lock.locked(30100));assert.equal(lock.remaining(99999),0);
});
