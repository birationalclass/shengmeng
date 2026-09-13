const assert=require('node:assert/strict');
global.window=global;const path=require('node:path').resolve(__dirname,'..');
for(const name of ['polyhedra','geometry','timeline','camera'])require(path+'/opening-'+name+'.js');
const P=CourseOpeningPolyhedra;
for(const solid of P.solids){
 assert.equal(solid.vertices.length-solid.edges.length+solid.faces.length,2);
 for(const v of solid.vertices)assert.ok(Math.abs(Math.hypot(...v)-1)<1e-12);
 for(const face of solid.faces){
  for(const id of face.ids)assert.ok(Math.abs(solid.vertices[id].reduce((s,x,i)=>s+x*face.normal[i],0)-face.height)<1e-10);
  for(const v of solid.vertices)assert.ok(v.reduce((s,x,i)=>s+x*face.normal[i],0)<=face.height+1e-10);
 }
 for(const [a,b] of solid.edges)assert.ok(Math.abs(Math.hypot(...solid.vertices[a].map((x,i)=>x-solid.vertices[b][i]))-solid.edgeLength)<1e-10);
 assert.ok(solid.edges.every(([a,b])=>solid.faces.filter(f=>f.ids.includes(a)&&f.ids.includes(b)).length===2));
}
const g=CourseOpeningGeometry,positions=g.create3D(6),normals=g.createNormals(6);
assert.equal(positions.length,g.count*3);
for(let i=0;i<g.count;i++){assert.ok(Math.abs(Math.hypot(...normals.subarray(i*3,i*3+3))-1)<1e-6);assert.ok(positions.subarray(i*3,i*3+3).every(Number.isFinite));}
const t=CourseOpeningTimeline.create({holds:[18000],transitions:[12000]});
for(const direction of [1,-1]){t.setDirection(direction,true);for(const time of [-90000,-1,0,17999,18000,29999,30000,70000]){const s=t.seek(time);assert.equal(s.moving,false);assert.equal(s.progress,1);assert.equal(s.holdDuration,30000);}}
const route={holds:[20000,20000],starts:[0,30000],transitions:[10000,10000],duration:60000,sceneIds:[5,6]};
CourseOpeningCamera.setFocuses(Array.from({length:7},()=>[0,0,0]));
for(let position=0;position<60000;position+=250){const p=CourseOpeningCamera.sampleTimeline({position,scene:6,from:6,to:6,moving:false},route);assert.ok(p.zoom<=2.3500001);assert.ok([...p.target,...p.angles,p.zoom].every(Number.isFinite));}
console.log('PASS: five exact convex solids, equal edges, closed two-manifold faces, 72,000 finite surface samples, unit normals, stationary single selection, no accidental E8 macro in filtered route');
const model=P.sample(72000),before=model.positions.slice(),normalsBefore=model.normals.slice();
for(let id=0;id<5;id++){
 const origin=[model.centres[id][0],model.centres[id][1],4];
 assert.equal(model.pick(origin,[0,0,-1]),id,'centre ray selects each of the five solids');
}
assert.equal(model.pick([3,3,4],[0,0,-1]),-1,'empty background is not draggable');
model.rotateSolid(1,[.3,.8,.2],.9);
let moved=0;
for(let i=0;i<model.solidIds.length;i++){
 const k=i*3;
 if(model.solidIds[i]!==1){assert.deepEqual(model.positions.subarray(k,k+3),before.subarray(k,k+3));assert.deepEqual(model.normals.subarray(k,k+3),normalsBefore.subarray(k,k+3));}
 else{
  const c=model.centres[1];
  const oldRadius=Math.hypot(...before.subarray(k,k+3).map((v,j)=>v-c[j])),newRadius=Math.hypot(...model.positions.subarray(k,k+3).map((v,j)=>v-c[j]));
  assert.ok(Math.abs(oldRadius-newRadius)<1e-6,'rotation preserves shape and centre');
  assert.ok(Math.abs(Math.hypot(...model.normals.subarray(k,k+3))-1)<1e-6);
  if(Math.hypot(...model.positions.subarray(k,k+3).map((v,j)=>v-before[k+j]))>.01)moved++;
 }
}
assert.ok(moved>10000);
assert.equal(model.pick([0,.37,4],[0,0,-1]),1,'rotated cube remains selectable');
const camera={angles:[.2,-.3,.1],zoom:1.8,target:[.1,-.1,0],perspective:1};
for(const [width,height] of [[1280,720],[390,844]]){
 const ray=P.screenRay(width/2,height/2,width,height,camera,.4);
 assert.ok([...ray.origin,...ray.direction].every(Number.isFinite));assert.ok(Math.abs(Math.hypot(...ray.direction)-1)<1e-12);
}
for(let n=0;n<500;n++)model.rotateSolid(1,[.3,.8,.2],.008);
assert.ok(Math.abs(Math.hypot(...model.orientations()[1])-1)<1e-12,'many drags preserve a unit quaternion');
model.reset();assert.deepEqual(model.positions,before);assert.deepEqual(model.normals,normalsBefore);
console.log('PASS: five independent picks; only the selected solid rotates; rigid geometry, normals, repeated drags and reset');
