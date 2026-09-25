import test from 'node:test';import assert from 'node:assert/strict';
import {FrameQuality} from './frame-quality.js';
function trial(){const b=new FrameQuality();let now=0;return {b,run(ms,duration,options={}){const end=now+duration;while(now<end){now+=ms;b.sample(ms,now,options);}return b.level;}};}
test('30 FPS with no GPU timing reduces effects first, then reading resolution',()=>{
 const t=trial();assert.equal(t.run(1000/30,2200),1);
 assert.deepEqual(t.b.settings({reading:true}),{scale:1,cloud:'low',shadow:1024,simpleWater:true,particles:true});
 t.run(1000/30,12000);assert.equal(t.b.level,5);
 const s=t.b.settings({reading:true});assert.equal(s.scale,.75);assert.equal(s.cloud,'off');assert.equal(s.shadow,0);assert(!s.particles);
 assert.equal(t.b.stats.target,60);assert(Math.abs(t.b.stats.fps-30)<.01);
});
test('fluctuating 20–40 FPS falls back without needing a visible performance panel',()=>{
 const b=new FrameQuality();let now=0;
 for(let i=0;i<600;i++){const ms=i%2?25:50;now+=ms;b.sample(ms,now);}
 assert.equal(b.level,5);assert.equal(b.settings().scale,.7);
});
test('short stalls and background gaps do not cause a quality spiral',()=>{
 const t=trial();t.run(1000/60,5000);t.run(200,200);t.run(1000/60,5000);assert.equal(t.b.level,0);
 t.run(1000,10000,{active:false});t.run(1000/60,5000);assert.equal(t.b.level,0);
});
test('recovery is slow and a failed recovery has a cooldown',()=>{
 const t=trial();t.run(1000/30,5000);const low=t.b.level;assert(low>0);
 t.run(1000/60,24000);assert.equal(t.b.level,low-1);
 t.run(1000/30,2300);assert.equal(t.b.level,low);assert(t.b.retryAt>t.b.changedAt);
 t.run(1000/60,30000);assert.equal(t.b.level,low);
});
test('fixed quality and 30 FPS target are honored; a 60 Hz screen is not forced to 120',()=>{
 const t=trial();t.run(1000/30,12000,{targetFPS:30});assert.equal(t.b.level,0);
 t.run(1000/60,12000,{targetFPS:120});assert.equal(t.b.stats.target,60);assert.equal(t.b.level,0);
 t.run(1000/30,6000);assert(t.b.level>0);t.run(1000/30,2000,{enabled:false});assert.equal(t.b.level,0);
});
