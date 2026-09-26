import assert from 'node:assert/strict';
import {KeyboardMotion} from './keyboard-motion.js';
function simulate(hz,seconds,keys){const m=new KeyboardMotion();let v;for(let i=0;i<hz*seconds;i++)v=m.update(new Set(keys),1/hz);return {m,v};}
for(const hz of [30,60,120]){
 const {m,v}=simulate(hz,2,['w']);assert.ok(v.forward<4.001&&v.forward>3.9);
 for(let i=0;i<hz*6.5;i++)m.update(new Set(['w']),1/hz);assert.ok(m.velocity[0]>11.8&&m.velocity[0]<=12);
 const old=m.velocity[0];m.update(new Set(['s']),1/hz);assert.ok(m.velocity[0]>0&&m.velocity[0]<old);assert.equal(m.held,0);
 for(let i=0;i<hz;i++)m.update(new Set(),1/hz);assert.ok(Math.abs(m.velocity[0])<.01);
 m.reset();assert.deepEqual(m.velocity,[0,0,0]);
}
const diagonal=simulate(60,2,['w','e']).v;assert.ok(Math.hypot(diagonal.forward,diagonal.right)<=4.001);
console.log('PASS: 2s normal speed, gradual 4–12m/s acceleration, smooth reversal/release, diagonal cap and 30/60/120Hz consistency');
