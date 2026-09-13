const assert=require('node:assert/strict');global.window=global;
for(const name of ['camera','timeline','polyhedra','topology'])require('../opening-'+name+'.js');
const C=CourseOpeningCamera;
// Timing must be three seconds at every supported morph speed and in either direction.
assert.equal(C.groupReturnMs,3000);
for(const scene of [6,7])for(const speed of [.25,.5,.75,1,1.5])for(const other of [3,4,5,8,9]){
 const duration=5000/speed;
 for(const elapsed of [0,100,250,500,750,999,1000,1500,2999,3000,duration]){
  const forward=C.groupWeight({from:other,to:scene,moving:true,progress:elapsed/duration},duration);
  const reverse=C.groupWeight({from:scene,to:other,moving:true,progress:1-elapsed/duration},duration);
  assert.ok(Math.abs(forward-reverse)<1e-12);
  if(elapsed>=3000)assert.equal(forward,1);
  if(elapsed>0&&elapsed<3000)assert.ok(forward>0&&forward<1);
  if(elapsed===0)assert.equal(forward,0);
 }
}
for(const order of [[3,5,6,7,9],[6],[6,9],[9,6],[3,6]]){
 const t=CourseOpeningTimeline.create({holds:order.map(()=>20000),transitions:order.map(()=>10000)});
 let previous;
 for(let time=0;time<=t.duration;time+=10){
  const state=t.seek(time),mapped={...state,from:order[state.from],to:order[state.to],scene:order[state.scene]},w=C.groupWeight(mapped,10000);
  assert.ok(w>=0&&w<=1);
  if(previous!==undefined)assert.ok(Math.abs(w-previous)<.019,'continuous at scene/hold/loop boundaries');
  if(!state.moving)assert.equal(w,[6,7].includes(mapped.scene)?1:0);
  previous=w;
 }
}
const view={angles:[.48,-.7,.03],zoom:8,target:[.6,-.3,.2],perspective:1};
const full=C.frameGroup(view,1);
assert.equal(full.zoom,1);assert.deepEqual(full.target,[0,0,0]);
assert.deepEqual(full.angles,view.angles);assert.equal(full.perspective,view.perspective);
assert.deepEqual(C.frameGroup(view,0),view);
// A sphere containing every rotated solid bounds its perspective projection at
// ANY orbit/spin angle. Verify generous viewport margins in landscape and portrait.
const model=CourseOpeningPolyhedra.sample(72000);
const topology=CourseOpeningTopology.sample(1000);
const radius=Math.max(...model.centres.map(p=>Math.hypot(...p)+.269),...topology.centres.map(p=>Math.hypot(...p)+.441));
const projectedRadius=radius/Math.sqrt(1-(radius/3.9)**2);
for(const [width,height] of [[1920,1080],[1280,900],[844,390],[390,844],[320,740]]){
 const aspect=width/height,fit=Math.min(.68,aspect*.84),t=Math.max(0,Math.min(1,(aspect-.8)/.5)),centre=.05+.15*t*t*(3-2*t);
 assert.ok(projectedRadius*fit/aspect<.9,'all grouped objects fit horizontally at any angle');
 assert.ok(projectedRadius*fit+centre<.9,'all grouped objects fit vertically at any angle');
}
console.log('PASS: three-second full framing at every morph speed; reverse playback, single selection, loop continuity; unchanged rotation and perspective; all grouped objects fit desktop/mobile at any angle');
