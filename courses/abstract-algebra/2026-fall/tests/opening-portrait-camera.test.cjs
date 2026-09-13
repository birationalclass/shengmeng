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
  assert.ok(a>=previous-1e-12);previous=a;if(p>=.45)assert.equal(a,1);
 }
 assert.equal(C.portraitWeight({from:scene,to:9,moving:true,progress:0}),0);
 assert.equal(C.portraitWeight({from:9,to:scene,moving:true,progress:1}),0);
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
console.log('PASS: portrait lock completes before formation; forward/reverse transitions, single selection and loop boundaries are continuous');
