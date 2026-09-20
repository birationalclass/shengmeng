import {updateArchitecturalMotion} from '../architectural-motion.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../../3d/vendor/three.module.js';
import {AtlasScene} from '../../test-module/scene.mjs';
import {replaceDomain} from '../enchanted-domains.mjs';
import {owlPose,updateOwls} from '../owls.mjs';
import {batchBuiltDomain} from '../static-batches.mjs';
function build(index){const a=Object.create(AtlasScene.prototype);a.materials=Object.fromEntries(['stone','paper','dark','gold','wood','jade','brass','red'].map(n=>[n,new T.MeshStandardMaterial()]));a.rotating=[];a.detailMotion=[];const p=new T.Group();replaceDomain(a,p,index);p.updateMatrixWorld(true);return {a,p};}
test('campus and five castle domains keep the usable board volume unobstructed, including mesh extents',()=>{const usable=new T.Box3(new T.Vector3(-5.6,1.4,-5.6),new T.Vector3(5.6,2.3,5.6));for(const i of [0,2,3,4,5,6]){const {p}=build(i);p.traverse(o=>{if(o.isMesh)assert.ok(!new T.Box3().setFromObject(o).intersectsBox(usable),`region ${i}: ${o.geometry.type}`);});}});
test('wizard court has opposing armies of all six piece types; mechanical scene retains five gears',()=>{const {p}=build(3);const pieces=[];p.traverse(o=>{if(o.userData.army)pieces.push(o);});assert.equal(pieces.length,16);assert.equal(new Set(pieces.map(o=>o.userData.landmark)).size,6);const {a}=build(4);assert.equal(a.rotating.filter(o=>o.object.userData.gearTrain).length,5);});
test('owls keep flying after static batching, and reduced motion fixes body and wings',()=>{const {a,p}=build(6),board={content:p,lift:new T.Group(),glow:new T.Group()};batchBuiltDomain(a,board);assert.equal(a.owls.length,3);for(const o of a.owls)o.root.traverse(m=>{if(m.isMesh)assert.ok(!board.batchedSources.includes(m));});
 updateOwls(a.owls,2,false);const before=a.owls.map(o=>o.root.position.toArray());updateOwls(a.owls,9,false);a.owls.forEach((o,i)=>assert.notDeepEqual(o.root.position.toArray(),before[i]));
 updateOwls(a.owls,20,true);const frozen=a.owls.map(o=>[...o.root.position.toArray(),o.body.rotation.z,...o.wings.map(w=>w.rotation.z)]);updateOwls(a.owls,100,true);a.owls.forEach((o,i)=>assert.deepEqual([...o.root.position.toArray(),o.body.rotation.z,...o.wings.map(w=>w.rotation.z)],frozen[i]));
});
test('owls fly low outside the castle and never cover the board in the default playing view',()=>{
 const camera=new T.PerspectiveCamera(40,1280/720,.1,1000);camera.position.set(0,36.65,33.975);camera.lookAt(0,1,3.5);camera.updateMatrixWorld(true);
 const bounds=(points)=>{const ps=points.map(p=>p.project(camera));return {left:Math.min(...ps.map(p=>p.x)),right:Math.max(...ps.map(p=>p.x)),bottom:Math.min(...ps.map(p=>p.y)),top:Math.max(...ps.map(p=>p.y))};};
 const board=bounds([-5.9,5.9].flatMap(x=>[-5.9,5.9].map(z=>new T.Vector3(x,1.595,z))));
 for(let t=0;t<180;t+=.1)for(let i=0;i<3;i++){
  const p=owlPose(t,i);assert.ok(Object.values(p).every(Number.isFinite));assert.ok(Math.hypot(p.x,p.z)>=13.8-1e-9);assert.ok(p.y>=2.55&&p.y<=3.05);
  const bird=bounds([-1.7,1.7].flatMap(dx=>[-.7,.7].flatMap(dy=>[-1.7,1.7].map(dz=>new T.Vector3(p.x+dx,p.y+dy,p.z+dz)))));
  assert.ok(bird.left>board.right||bird.right<board.left||bird.bottom>board.top||bird.top<board.bottom,'The owl silhouette must clear the projected board');
 }
});

test('wizard gestures stay outside the board, survive batching, and rest under reduced motion',()=>{const {a,p}=build(3),board={content:p,lift:new T.Group(),glow:new T.Group()};batchBuiltDomain(a,board);const gestures=a.detailMotion.filter(m=>m.mode==='gesture');assert.ok(gestures.length>=16);for(const m of gestures)m.object.traverse(o=>assert.ok(!board.batchedSources.includes(o)));const usable=new T.Box3(new T.Vector3(-5.9,1.4,-5.9),new T.Vector3(5.9,2.3,5.9));for(let t=0;t<12;t+=.2){updateArchitecturalMotion(a.detailMotion,t);p.updateMatrixWorld(true);for(const m of gestures)assert.ok(!new T.Box3().setFromObject(m.object).intersectsBox(usable));}updateArchitecturalMotion(a.detailMotion,7,true);for(const m of gestures)assert.equal(m.object.rotation[m.axis],m.base);});
