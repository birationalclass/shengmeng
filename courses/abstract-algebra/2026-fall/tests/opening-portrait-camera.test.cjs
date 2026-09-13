const assert=require('node:assert/strict');global.window=global;
require('../opening-camera.js');require('../opening-timeline.js');
const C=CourseOpeningCamera;
for(const scene of [3,4,5,6,7,8])assert.equal(C.portraitWeight({scene,moving:false}),0);
assert.equal(C.portraitWeight({scene:9,moving:false}),1);
for(const scene of [3,4,5,6,7,8]){
 let previous=0;
 for(let i=0;i<=1000;i++){
  const p=i/1000,a=C.portraitWeight({from:scene,to:9,moving:true,progress:p}),b=C.portraitWeight({from:9,to:scene,moving:true,progress:1-p});
  assert.ok(Math.abs(a-b)<1e-12,'forward/reverse changes follow the same envelope');
  assert.ok(a>=previous-1e-12);previous=a;if(p<1)assert.ok(a<1);
 }
 assert.equal(C.portraitWeight({from:scene,to:9,moving:true,progress:0}),0);
 assert.equal(C.portraitWeight({from:9,to:scene,moving:true,progress:1}),0);
}
const ease=t=>t*t*t*(t*(t*6-15)+10);
// The same original return trajectory now takes exactly three times as long,
// at every supported morph speed, including outgoing and reverse transitions.
assert.equal(C.portraitTransitionScale,1.35);
for(const speed of [.25,.5,.75,1,1.5])for(const base of [4200,5200,5400,5000]){
 const oldDuration=base/speed,newDuration=oldDuration*C.portraitTransitionScale;
 for(let i=0;i<=100;i++){
  const oldElapsed=oldDuration*.45*i/100,newElapsed=oldElapsed*3;
  const forward=C.portraitWeight({from:3,to:9,moving:true,progress:newElapsed/newDuration});
  const reverse=C.portraitWeight({from:9,to:3,moving:true,progress:1-newElapsed/newDuration});
  assert.ok(Math.abs(forward-ease(i/100))<1e-12);
  assert.ok(Math.abs(reverse-forward)<1e-12);
 }
}
// Default authoring poses use full 30-second holds plus separate transitions.
const transitions=[8400,8400,8400,10400,10800,10000,10000,10000,13500,13500];
const holds=Array(10).fill(30000);let duration=0;
const starts=holds.map((hold,i)=>{const start=duration;duration+=hold+transitions[i];return start;});
assert.equal(C.evidence().defaultHoldSeconds,30);
assert.equal(C.evidence().defaultCycleSeconds,duration/1000);
for(let scene=0;scene<10;scene++)for(const phase of [0,.25,.5,.75,1]){
 const expected=C.sampleTimeline({from:scene,to:scene,scene,moving:false,position:starts[scene]+phase*30000},{holds,transitions,starts,duration});
 assert.deepEqual(C.sample(scene,phase),expected);
}
for(const order of [[8,9,3],[9],[9,6,7],[3,9]]){
 const t=CourseOpeningTimeline.create({holds:order.map(()=>20000),transitions:order.map(()=>10000)});
 for(const direction of [-1,1]){
  t.setDirection(direction);let previous;
  for(let i=0;i<=t.duration;i+=25){
   const state=t.seek(i),mapped={...state,from:order[state.from],to:order[state.to],scene:order[state.scene]},w=C.portraitWeight(mapped);
   assert.ok(Number.isFinite(w)&&w>=0&&w<=1);if(previous!==undefined)assert.ok(Math.abs(w-previous)<.011,'no camera jump at a hold, scene switch or loop seam');
   if(!state.moving&&mapped.scene===9)assert.equal(w,1);
   previous=w;
  }
 }
}
console.log('PASS: portrait return runs at one-third speed; full 30-second holds exclude morphs; forward/reverse transitions, single selection and loop boundaries remain continuous');
