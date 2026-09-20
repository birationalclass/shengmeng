import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../../3d/vendor/three.module.js';
import {AtlasScene} from '../../test-module/scene.mjs';
import {landmark} from '../landmarks.mjs';
import {greatWall} from '../great-wall.mjs';
import {updateArchitecturalMotion} from '../architectural-motion.mjs';
function builder(){const a=Object.create(AtlasScene.prototype);a.materials=Object.fromEntries(['stone','paper','dark','gold','wood','jade','brass','red'].map(n=>[n,new T.MeshStandardMaterial()]));a.rotating=[];a.detailMotion=[];return a;}
test('every domain has articulated landmarks and reduced motion resets their joints',()=>{
 // The shared types cover the different landmark combinations of all eight domains.
 for(const type of ['well','fountain','pavilion','market','windmill','clocktower','greenhouse','observatory','gatehouse']){
  const a=builder(),parent=new T.Group();landmark(a,parent,type,0,0);assert.ok(a.detailMotion.length>0,type);
  const before=a.detailMotion.map(m=>m.object.position.toArray().concat(m.object.rotation.toArray().slice(0,3)));
  updateArchitecturalMotion(a.detailMotion,2.7,false);
  assert.ok(a.detailMotion.some((m,i)=>m.object.position.toArray().concat(m.object.rotation.toArray().slice(0,3)).some((v,k)=>Math.abs(v-before[i][k])>1e-6)),type);
  updateArchitecturalMotion(a.detailMotion,100,true);
  a.detailMotion.forEach((m,i)=>assert.deepEqual(m.object.position.toArray().concat(m.object.rotation.toArray().slice(0,3)),before[i],type));
 }
});
test('Great Wall forms a complete ring on the disk around the board and has moving flags',()=>{
 const a=builder(),root=new T.Group(),wall=greatWall(a,root);wall.updateMatrixWorld(true);let meshes=0;
 wall.traverse(o=>{if(!o.isMesh)return;meshes++;o.geometry.computeBoundingBox();const b=o.geometry.boundingBox;
  for(const x of [b.min.x,b.max.x])for(const y of [b.min.y,b.max.y])for(const z of [b.min.z,b.max.z]){
   const p=new T.Vector3(x,y,z).applyMatrix4(o.matrixWorld);assert.ok(Math.hypot(p.x,p.z)<13.05);assert.ok(Math.abs(p.x)>6||Math.abs(p.z)>6,'Wall must not intrude into the board');
  }
 });const segments=wall.children.filter(o=>o.userData.wallSegment);assert.equal(segments.length,64);assert.ok(segments[0].userData.wallSegment.height>segments[32].userData.wallSegment.height+1.9);for(let i=1;i<32;i++)assert.ok(segments[i].userData.wallSegment.height<segments[i-1].userData.wallSegment.height);assert.equal(segments[0].userData.wallSegment.start,0);assert.ok(Math.abs(segments.at(-1).userData.wallSegment.end-Math.PI*2)<1e-9);assert.equal(wall.children.filter(o=>o.userData.landmark==='great-wall-watchtower').length,8);assert.ok(meshes>200);assert.ok(a.detailMotion.length>=15);
});
