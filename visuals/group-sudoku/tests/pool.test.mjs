import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../../3d/vendor/three.module.js';
import {AtlasScene} from '../../test-module/scene.mjs';
import {ecnuCampus} from '../ecnu-campus.mjs';
import {boatPose,updatePoolBoats} from '../pool-boats.mjs';
import {batchBuiltDomain} from '../static-batches.mjs';
function build(){const a=Object.create(AtlasScene.prototype);a.materials=Object.fromEntries(['stone','paper','dark','gold','wood','jade','brass','red'].map(n=>[n,new T.MeshStandardMaterial()]));a.rotating=[];a.detailMotion=[];const p=new T.Group();ecnuCampus(a,p);p.updateMatrixWorld(true);return {a,p};}
test('the seal is below the water, four cherry trees remain, and no buildings remain',()=>{const {p}=build(),objects=[];p.traverse(o=>objects.push(o));const water=objects.find(o=>o.userData.landmark==='pool-water'),seal=objects.find(o=>o.userData.landmark==='ecnu-official-seal');assert.ok(new T.Box3().setFromObject(seal).max.y<water.position.y-.25);assert.equal(objects.filter(o=>o.userData.landmark==='cherry-tree').length,4);assert.ok(!objects.some(o=>/curtain-wall|teaching-wing|great-hall|spire|bridge/.test(o.userData.landmark||'')));});
test('three boats stay clear of the board and shore and do not get frozen by static batching',()=>{const {a,p}=build(),board={content:p,lift:new T.Group(),glow:new T.Group()};assert.equal(a.poolBoats.length,3);batchBuiltDomain(a,board);for(const boat of a.poolBoats)boat.root.traverse(o=>assert.ok(!board.batchedSources.includes(o)));
 for(let t=0;t<90;t+=.5){updatePoolBoats(a.poolBoats,t,false);p.updateMatrixWorld(true);for(const boat of a.poolBoats){const pose=boatPose(t,boat.index);assert.ok(Object.values(pose).every(Number.isFinite));const bb=new T.Box3().setFromObject(boat.root);assert.ok(!bb.intersectsBox(new T.Box3(new T.Vector3(-5.9,0,-5.9),new T.Vector3(5.9,2,5.9))));assert.ok(Math.hypot(pose.x,pose.z)+1<11.68);}}
 updatePoolBoats(a.poolBoats,10,true);const frozen=a.poolBoats.map(b=>b.root.position.toArray());updatePoolBoats(a.poolBoats,30,true);a.poolBoats.forEach((b,i)=>{assert.deepEqual(b.root.position.toArray(),frozen[i]);assert.equal(b.wake.visible,false);});
});
