import test from 'node:test';
import assert from 'node:assert/strict';
import {OceanBudget} from './ocean-budget.js';
function trial(){const b=new OceanBudget();b.configure('auto',60);let now=0;return {b,run(ms,duration,options={}){const end=now+duration;while(now<end){now+=ms;b.sample(ms,now,options);}return b.level;}};}
test('foreground FPS promotes gradually and drops heavy surf without GPU queries',()=>{
 const t=trial();assert.equal(t.b.level,0);
 assert.equal(t.run(1000/60,18000),1);assert.equal(t.run(1000/60,18000),2);
 assert.equal(t.run(40,5000),0);assert(t.b.stats.fps<30);
 assert.equal(t.run(1000/60,30000),0,'A failed expensive tier cannot immediately return');
 assert.equal(t.run(1000/60,40000),1);
});
test('background, indoor views and isolated stalls cannot trigger an expensive upgrade',()=>{
 const t=trial();t.run(1000/60,10000);t.run(1000/60,20000,{active:false});assert.equal(t.b.level,0);
 t.run(1000/60,40000,{eligible:false});assert.equal(t.b.level,0);
 t.run(1000/60,18000);assert.equal(t.b.level,1);
 t.run(250,250);t.run(1000/60,5000);assert.equal(t.b.level,1);
});
test('120 FPS preference respects measured browser cadence; real 120 Hz is recognized',()=>{
 const t=trial();t.b.configure('auto',120);t.run(1000/60,18000);
 assert.equal(t.b.stats.target,60);assert.equal(t.b.level,1);
 t.run(1000/120,4000);assert.equal(t.b.stats.target,120);
});
test('manual settings are honored and excessive GPU cost prevents speculative upgrades',()=>{
 const t=trial();t.run(1000/60,40000,{gpuMs:16});assert.equal(t.b.level,0);
 t.b.configure('study',60);t.run(100,10000);assert.equal(t.b.level,2);
 t.b.configure('lite',60);t.run(1000/60,40000);assert.equal(t.b.level,0);
 t.b.configure('auto',60);assert.equal(t.b.level,0);
});
