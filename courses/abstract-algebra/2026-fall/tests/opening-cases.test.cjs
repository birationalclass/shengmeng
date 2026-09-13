const assert=require('node:assert/strict');
global.window=global;
for(const name of ['polyhedra','topology','gauss','geometry','timeline','camera'])require('../opening-'+name+'.js');
const T=CourseOpeningTopology,G=CourseOpeningGauss,g=CourseOpeningGeometry;
const near=(a,b,t=1e-10)=>assert.ok(Math.hypot(...a.map((x,i)=>x-b[i]))<t);
// The seam glues with a half twist; the single boundary closes only after 4π.
for(let u=0;u<2*Math.PI;u+=.13)for(const v of [-T.halfWidth,0,T.halfWidth]){
 near(T.mobius(u+2*Math.PI,v),T.mobius(u,-v));
 near(T.mobius(u+4*Math.PI,v),T.mobius(u,v));
 const f=T.mobiusFrame(u,v);assert.ok(Math.abs(Math.hypot(...f.normal)-1)<1e-12);
 const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
 assert.ok(Math.abs(dot(f.du,f.normal))<1e-12&&Math.abs(dot(f.dv,f.normal))<1e-12);
 // The stated deformation retraction fixes the core throughout the homotopy.
 near(T.mobius(u,0),[T.radius*Math.cos(u),T.radius*Math.sin(u),0]);
}
assert.ok(Math.hypot(...T.mobius(0,T.halfWidth).map((x,i)=>x-T.mobius(2*Math.PI,T.halfWidth)[i]))>.2);
const m=T.sample(72000),before=m.positions.slice(),normalBefore=m.normals.slice();
function world(p,id){return T.pose(p,id).map((x,i)=>x+m.centres[id][i]);}
for(const id of [0,1]){
 const q=world(id?T.mobius(.8,.04):T.circle(0,0),id);
 assert.equal(m.pick([q[0],q[1],4],[0,0,-1]),id);
}
assert.equal(m.pick([-.5,.02,4],[0,0,-1]),-1,'the hole in S¹ is empty');
assert.equal(m.pick([3,3,4],[0,0,-1]),-1);
for(let i=0;i<72000;i++){
 assert.ok(m.positions.subarray(i*3,i*3+3).every(Number.isFinite));
 assert.ok(Math.abs(Math.hypot(...m.normals.subarray(i*3,i*3+3))-1)<1e-6);
}
for(const id of [0,1]){
 m.reset();m.rotateObject(id,[.3,.8,.2],.9);let moved=0;
 for(let i=0;i<72000;i++){
  const k=i*3,p=m.positions.subarray(k,k+3),b=before.subarray(k,k+3);
  if(m.objectIds[i]!==id){assert.deepEqual(p,b);assert.deepEqual(m.normals.subarray(k,k+3),normalBefore.subarray(k,k+3));}
  else{if(Math.hypot(...p.map((x,j)=>x-b[j]))>.01)moved++;
   near([Math.hypot(...p.map((x,j)=>x-m.centres[id][j]))],[Math.hypot(...b.map((x,j)=>x-m.centres[id][j]))],1e-6);
  }
 }
 assert.ok(moved>19000);
 for(let i=0;i<200;i++)m.rotateObject(id,[.2,.4,.9],.01);
 assert.ok(Math.abs(Math.hypot(...m.orientations()[id])-1)<1e-12);
}
m.reset();assert.deepEqual(m.positions,before);assert.deepEqual(m.normals,normalBefore);
console.log('PASS: half-twist seam, one connected boundary, unit normals, independent rigid dragging, picking through the hole, stable reset');
assert.equal(G.vertices.length,17);
assert.ok(Math.abs(G.cosine-Math.cos(2*Math.PI/17))<1e-14,'Gaussian periods construct the exact first angle');
assert.ok(G.evidence().closureError<1e-13);
for(let i=0;i<17;i++){
 const a=G.vertices[i],b=G.vertices[(i+1)%17];
 near([Math.hypot(...a)],[G.evidence().radius]);near([Math.hypot(...a.map((x,k)=>x-b[k]))],[G.side]);
 for(let j=0;j<i;j++)assert.ok(Math.hypot(...a.map((x,k)=>x-G.vertices[j][k]))>.25);
}
assert.equal(g.captions.length,10);assert.equal(CourseOpeningCamera.count,10);
for(const id of [7,8]){
 assert.equal(g.create3D(id).length,72000*3);assert.equal(g.create(id).length,72000*2);assert.equal(g.createNormals(id).length,72000*3);
 for(const x of g.create3D(id))assert.ok(Number.isFinite(x));
 for(let i=0;i<72000;i++)assert.ok(Math.abs(Math.hypot(...g.createNormals(id).subarray(i*3,i*3+3))-1)<1e-6);
 near(g.closeupFocus(id),[0,0,0]);
}
const camera=CourseOpeningCamera;
camera.setFocuses(Array.from({length:camera.count},()=>[0,0,0]));
for(const ids of [[7],[8],[7,8]]){
 const route={holds:ids.map(()=>20000),transitions:ids.map(()=>10000),starts:ids.map((_,i)=>i*30000),duration:ids.length*30000,sceneIds:ids};
 for(let position=0;position<route.duration;position+=250){
  const p=camera.sampleTimeline({position,scene:ids[0],from:ids[0],to:ids[0],moving:false},route);
  assert.ok([...p.angles,...p.target,p.zoom].every(Number.isFinite));assert.ok(p.zoom<=2.3500001);
 }
}
console.log('PASS: 17 distinct equally spaced vertices from square roots, 72,000 finite samples, stable-scene geometry/camera alignment and filtered routes');
