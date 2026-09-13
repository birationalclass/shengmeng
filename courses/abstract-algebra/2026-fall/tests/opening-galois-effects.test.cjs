const assert=require('node:assert/strict');global.window=global;
global.CourseOpeningGalois={leaves:Array.from({length:7},(_,i)=>({tag:i+2,centre:[-.6+.2*i,-.15+.08*(i%3)],radius:.1}))};
require('../opening-materials.js');const M=CourseOpeningMaterials;
const near=(a,b,tolerance=1e-10)=>assert.ok(Math.abs(a-b)<tolerance,`${a} != ${b}`);
// Only the independently tagged near person disperses, in straight outward rays.
for(const seed of [.01,.12,.31,.5,.67,.83,.99])for(const point of [[-.43,.04,.04],[-.47,-.50,.034],[-.42,-.19,.043],[-.43,-.245,.042]]){
 let lastRadius=0,lastAlpha=1,ray;
 for(let j=0;j<=100;j++){
  const value=M.storyLoss(point,j/100,seed);assert.ok(value.point.every(Number.isFinite));
  const d=value.point.map((v,k)=>v-point[k]),radius=Math.hypot(...d);
  assert.ok(radius>=lastRadius-1e-12);assert.ok(value.alpha<=lastAlpha+1e-12);
  if(radius>1e-5){if(!ray)ray=d.map(v=>v/radius);else d.forEach((v,k)=>near(v/radius,ray[k]));}
  const outward=[point[0]+.43,point[1]+.245];assert.ok(d[0]*outward[0]+d[1]*outward[1]>=-1e-12);
  lastRadius=radius;lastAlpha=value.alpha;
 }
 assert.ok(lastRadius>.77,'grain travels a substantial distance rather than fading in place');assert.equal(lastAlpha,0);
 const mid=M.storyLoss(point,.5,seed);assert.ok(mid.alpha>.4,'outward travel is visible before the late fade');
}
for(const point of [[.47,-.2,.009],[-.8,-.4,.02],[.3,.1,.071]])for(const loss of [0,.2,.7,1])assert.deepEqual(M.storyLoss(point,loss,.4),{point,alpha:1});
// Responsive compact framing must be exactly the same physical trajectory.
for(const fit of [[1,0],[.66,-.34]])for(const loss of [.25,.6,1]){
 const base=[-.44,-.22,.041],compact=base.map((v,i)=>v*fit[0]+(i===1?fit[1]:0));
 const a=M.storyLoss(base,loss,.45),b=M.storyLoss(compact,loss,.45,fit);
 a.point.forEach((v,i)=>near(b.point[i],v*fit[0]+(i===1?fit[1]:0)));near(a.alpha,b.alpha);
}
// Each leaf is coherent, falls over time, and removes its identifier from depth.
for(let i=0;i<7;i++){
 const spec=CourseOpeningGalois.leaves[i],z=.03*(i+2)+.011;
 const a=[spec.centre[0]-.035,spec.centre[1]+.02,z],b=[spec.centre[0]+.041,spec.centre[1]-.014,z];
 const clock=.4+.8*i,period=14+.7*i;
 assert.deepEqual(M.storyLeaves(a,-1),{point:a,alpha:1});
 const early=M.storyLeaves(a,clock+period*.2),late=M.storyLeaves(a,clock+period*.7);
 assert.ok(late.point[1]<early.point[1]-.4,'whole leaf descends clearly');
 for(const elapsed of [0,clock,clock+1,clock+period*.4,clock+period*.85,clock+period,clock+period+1]){
  const x=M.storyLeaves(a,elapsed),y=M.storyLeaves(b,elapsed);
  near(Math.hypot(...x.point.map((v,k)=>v-y.point[k])),Math.hypot(...a.map((v,k)=>v-b[k])));
  near(x.alpha,y.alpha);assert.ok(x.alpha>=0&&x.alpha<=1);assert.ok(Math.abs(x.point[2])<.07,'leaf id is not rendered as depth');
  const fit=[.66,-.34],c=a.map((v,k)=>v*fit[0]+(k===1?fit[1]:0)),mapped=M.storyLeaves(c,elapsed,fit);
  x.point.forEach((v,k)=>near(mapped.point[k],v*fit[0]+(k===1?fit[1]:0)));near(x.alpha,mapped.alpha);
 }
 assert.ok(M.storyLeaves(a,clock+period-.001).alpha<1e-6);assert.ok(M.storyLeaves(a,clock+period+.001).alpha<1e-5,'cycle resets only while invisible');
}
for(const elapsed of [-1,0,5,20,50]){
 const point=[.2,-.2,.012];assert.deepEqual(M.storyLeaves(point,elapsed),{point,alpha:1});
}
console.log('PASS: near figure disperses radially along seeded straight rays with delayed fade; landscape untouched; coherent falling leaves, transparent cycle reset, tag depth removal and compact-fit invariance');
