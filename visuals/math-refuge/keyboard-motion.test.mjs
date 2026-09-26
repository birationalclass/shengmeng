import assert from 'node:assert/strict';
import {KeyboardMotion} from './keyboard-motion.js';
const key=(...k)=>new Set(k);
for(const hz of [30,60,120]){
 const m=new KeyboardMotion(),dt=1/hz;
 for(let i=0;i<hz;i++)m.update(key('w'),dt);
 assert.ok(m.velocity[0]>4,'acceleration begins during first second');
 for(let i=0;i<hz*6;i++)m.update(key('w'),dt);
 assert.ok(m.velocity[0]>11.8&&m.velocity[0]<=12);
 let held=m.held;
 for(const keys of [key('w','q'),key('q'),key('e'),key('e','a'),key('e',' '),key(' '),key('x'),key('x',' '),key('w','shift')]){
  m.update(keys,dt);assert.ok(m.held>held,'direction/chord changes retain acceleration');held=m.held;
 }
 m.update(key('w'),dt);const old=m.velocity[0];m.update(key('s'),dt);assert.ok(m.velocity[0]<old);
 for(let i=0;i<hz;i++)m.update(key(),dt);
 assert.equal(m.held,0);assert.ok(Math.hypot(...m.velocity)<.01);
 for(let i=0;i<hz*8;i++)m.update(key('w','e'),dt);
 assert.ok(Math.hypot(...m.velocity)<=12.00001,'diagonals have the same speed cap');
 m.reset();assert.deepEqual(m.velocity,[0,0,0]);assert.equal(m.held,0);
}
console.log('PASS: immediate acceleration, uninterrupted chord/direction changes, opposing held keys, release reset, diagonal cap at 30/60/120Hz');
