import {test} from 'node:test';
import assert from 'node:assert/strict';
import {Vector3} from '../3d/vendor/three.module.js';
import {configureCameraInput} from './camera-input.js';
test('left drag turns in place and keeps a bounded yaw rate after reducing mouse sensitivity by 20%',()=>{
 const handlers={},events=[],position=new Vector3(5,3,9),controls={mouseButtons:{LEFT:0},enabled:true,object:{position},target:new Vector3(5,3,-11),update(){},dispatchEvent:e=>events.push(e.type)};
 const element={addEventListener:(type,fn)=>{(handlers[type]??=[]).push(fn);},removeEventListener(){},setPointerCapture(){},hasPointerCapture:()=>false};
 const input=configureCameraInput(controls,element),send=(type,extra)=>handlers[type].forEach(fn=>fn({button:0,pointerType:'mouse',pointerId:1,clientX:0,clientY:0,timeStamp:0,preventDefault(){},stopImmediatePropagation(){},...extra}));
 send('pointerdown',{});send('pointermove',{clientX:1000,timeStamp:16});send('pointerup',{clientX:1000,timeStamp:17});
 assert.deepEqual(position.toArray(),[5,3,9]);const direction=controls.target.clone().sub(position);assert.ok(Math.abs(Math.atan2(direction.x,-direction.z))<=1.44*.016+1e-8);assert.ok(Math.abs(Math.atan2(direction.x,-direction.z))>.9*.016,'fast drag must be more responsive than the old cap');assert.deepEqual(events,['start','end']);assert.equal(controls.mouseButtons.LEFT,null);input.dispose();assert.equal(controls.mouseButtons.LEFT,0);
});
