import test from 'node:test';
import assert from 'node:assert/strict';
import {RenderBudget,roundedDetailLevel,createGpuTimer} from './render-budget.js';

test('screen-space LOD retains a model and has a stable transition band',()=>{
 assert.equal(roundedDetailLevel(20),0);assert.equal(roundedDetailLevel(5),1);
 assert.equal(roundedDetailLevel(7,1),1);assert.equal(roundedDetailLevel(7,0),0);
 assert.equal(roundedDetailLevel(9,1),0);
 for(const size of [0,.001,1,4,100,1e6])assert([0,1].includes(roundedDetailLevel(size)));
});
test('resolution uses sustained GPU pressure, protects reading, and recovers slowly',()=>{
 const budget=new RenderBudget();let now=0;
 const feed=(ms,count)=>{for(let i=0;i<count;i++){now+=200;budget.sample(ms,now);budget.update(now);}};
 feed(8,40);assert.equal(budget.scale,1);
 feed(40,100);assert.equal(budget.scale,.76);
 budget.update(now,{reading:true});assert.equal(budget.scale,.96);
 for(let i=0;i<50;i++){now+=200;budget.sample(40,now);budget.update(now,{reading:true});}assert.equal(budget.scale,.96);
 feed(8,80);assert.equal(budget.scale,1);
 budget.sample(100,now+200);budget.update(now+200);assert.equal(budget.scale,1,'One expensive frame is not a reason to resize');
 feed(40,30);assert(budget.scale<1);budget.update(now,{enabled:false});assert.equal(budget.scale,1);
});
test('missing, invalid or stale GPU timing cannot lower quality',()=>{
 const budget=new RenderBudget();
 for(let t=0;t<60000;t+=200){budget.sample(NaN,t);budget.sample(300,t);budget.update(t);}assert.equal(budget.scale,1);
 for(let i=1;i<=8;i++)budget.sample(40,i*200);budget.update(10000);assert.equal(budget.scale,1);
 budget.sample(40,10200);assert.equal(budget.samples.length,1,'Do not reuse samples from another browser session');
});
test('GPU timer never waits for incomplete results and discards disjoint or expired queries',()=>{
 const ext={TIME_ELAPSED_EXT:1,QUERY_COUNTER_BITS_EXT:2,GPU_DISJOINT_EXT:3};
 let available=false,disjoint=false,created=0,deleted=0,reads=0,begins=0;
 const gl={CURRENT_QUERY:4,QUERY_RESULT_AVAILABLE:5,QUERY_RESULT:6,getExtension:()=>ext,getQuery:(_t,p)=>p===2?32:null,
  createQuery:()=>({id:++created}),deleteQuery(){deleted++;},beginQuery(){begins++;},endQuery(){},isContextLost:()=>false,
  getParameter:()=>disjoint,getQueryParameter(_q,p){if(p===5)return available;reads++;return 23000000;}};
 const timer=createGpuTimer(gl);assert(timer.supported);timer.begin(200);timer.end();
 assert.equal(timer.poll(216),null);assert.equal(reads,0);timer.begin(500);assert.equal(created,1,'At most one pending query');
 available=true;assert.equal(timer.poll(516),23);assert.equal(deleted,1);
 timer.begin(800);timer.end();disjoint=true;assert.equal(timer.poll(820),null);assert.equal(reads,1);
 disjoint=false;available=false;timer.begin(1200);timer.end();assert.equal(timer.poll(3000),null);assert.equal(deleted,3);
 timer.dispose();assert.equal(begins,3);
 const unsupported=createGpuTimer({getExtension:()=>null});unsupported.begin(1000);unsupported.end();assert.equal(unsupported.poll(2000),null);
});
