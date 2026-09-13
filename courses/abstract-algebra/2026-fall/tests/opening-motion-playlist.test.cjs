const assert=require('node:assert/strict');global.window=global;
for(const name of ['motion','playlist','polyhedra','topology'])require('../opening-'+name+'.js');
let seed=1234;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
const motion=CourseOpeningMotion.create(random),initial=motion.evidence();
assert.equal(new Set(initial.directions).size,2);
for(const axes of Object.values(initial.axes))for(const axis of axes)assert.ok(Math.abs(Math.hypot(...axis)-1)<1e-12);
assert.equal(new Set(Object.values(initial.axes).flat().map(a=>a.join(','))).size,7);
for(const scene of [6,7])for(const step of motion.objectSteps(scene,.25))assert.equal(step.angle,scene===6?.5:.25);
for(const from of [3,4,5,6,7,8,9])for(const to of [3,4,5,6,7,8,9]){
 assert.equal(motion.sceneDirection({from,to,moving:true,progress:0}),initial.directions[from]);
 assert.equal(motion.sceneDirection({from,to,moving:true,progress:1}),initial.directions[to]);
}
const models={6:CourseOpeningPolyhedra.sample(1000),7:CourseOpeningTopology.sample(1000)};
for(const scene of [6,7]){
 const model=models[scene],before=model.positions.slice();
 for(const angle of [.2,-.2])for(const step of motion.objectSteps(scene,angle)){
  if(scene===6)model.rotateSolid(step.index,step.axis,step.angle);else model.rotateObject(step.index,step.axis,step.angle);
 }
 for(let i=0;i<before.length;i++)assert.ok(Math.abs(before[i]-model.positions[i])<1e-6,'reverse playback restores every object');
}
assert.deepEqual(motion.evidence(),initial,'directions never change during playback');
const ids=[3,4,5,6,7,8,9];
for(const randomized of [false,true]){
 const p=CourseOpeningPlaylist.create({sceneIds:ids,randomized,seed:1949});
 const distinct=new Set();
 for(let cycle=-20;cycle<=100;cycle++){
  const order=p.order(cycle);assert.deepEqual([...order].sort(),ids,'every selected scene exactly once per cycle');
  assert.deepEqual(p.order(cycle),order,'reverse playback retrieves the same deck');distinct.add(order.join(','));
  if(!randomized)assert.deepEqual(order,ids);
 }
 if(randomized)assert.ok(distinct.size>100,'new shuffled decks across cycles');
}
assert.deepEqual(CourseOpeningPlaylist.create({sceneIds:[7],randomized:true,seed:1}).order(12),[7]);
console.log('PASS: seven stable independent random axes; signed scene rotation; doubled polyhedron self-spin; reversible object motion; complete shuffled rounds and stable reverse playback');
