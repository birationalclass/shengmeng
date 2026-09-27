import assert from 'node:assert/strict';
import {horizontalSpeedLimit,AltitudeDialRange} from './altitude-speed.js';
import {KeyboardMotion} from './keyboard-motion.js';
assert.equal(horizontalSpeedLimit(0),100);assert.equal(horizontalSpeedLimit(10),100);assert.equal(horizontalSpeedLimit(1000),400);assert.equal(horizontalSpeedLimit(5000),400);
let previous=100;for(let h=0;h<=1000;h++){const v=horizontalSpeedLimit(h);assert(v>=previous&&v-previous<.46);previous=v;}
for(const hz of [30,60,120])for(const height of [0,505,1000]){
 const m=new KeyboardMotion();for(let i=0;i<hz*12;i++)m.update(new Set(['w','e']),1/hz,height);
 assert(Math.abs(Math.hypot(m.velocity[0],m.velocity[1])*3.6-horizontalSpeedLimit(height))<.01);
 const vertical=new KeyboardMotion();for(let i=0;i<hz*12;i++)vertical.update(new Set([' ']),1/hz,height);
 assert(Math.abs(vertical.velocity[2]*3.6-100)<.01);
 for(let i=0;i<hz*3;i++)m.update(new Set(),1/hz,height);assert.equal(Math.hypot(...m.velocity),0);
}
const r=new AltitudeDialRange();let b=r.update(151,.016);assert.equal(b.max,200);assert.equal(b.min,100);assert(b.displayMax>100&&b.displayMax<104);
for(const v of [150,149,151,146])assert.equal(r.update(v,.016).max,200,'hysteresis prevents threshold chatter');
assert.equal(r.update(144,.016).max,150);
for(let i=0;i<600;i++)b=r.update(400,1/60);assert.equal(b.max,400);assert.equal(b.min,300);assert(Math.abs(b.displayMax-400)<.001);
assert.equal(r.update(100,.016).min,0);
console.log('PASS altitude limits, frame-independent motion, diagonal limits, vertical speed, stop, dial steps and hysteresis');
