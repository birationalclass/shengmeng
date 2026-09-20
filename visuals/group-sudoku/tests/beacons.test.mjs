import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../../3d/vendor/three.module.js';
import {AtlasScene} from '../../test-module/scene.mjs';
import {greatWall} from '../great-wall.mjs';
import {beaconProgress,syncWallBeacons,updateWallBeacons} from '../board-beacons.mjs';
import {batchBuiltDomain} from '../static-batches.mjs';
test('only wall braziers light by filling progress, survive batching, and extinguish on clearing',()=>{
 const a=Object.create(AtlasScene.prototype);a.materials=Object.fromEntries(['stone','paper','dark','gold','wood','jade','brass','red'].map(n=>[n,new T.MeshStandardMaterial()]));a.rotating=[];a.detailMotion=[];const content=new T.Group();greatWall(a,content);const wall=a.wallBeacons,values=Array(81).fill(0);assert.equal(wall.length,8);
 syncWallBeacons(wall,values);assert.ok(wall.every(p=>!p.fire.visible));values.fill(9);syncWallBeacons(wall,values);assert.ok(wall.every(p=>p.fire.visible));updateWallBeacons(wall,2,.1);assert.ok(wall.every(p=>p.ignition>0));values[13]=0;syncWallBeacons(wall,values);assert.equal(wall.filter(p=>p.fire.visible).length,7);assert.deepEqual(beaconProgress(values),{filled:80,total:81,wallLit:7});updateWallBeacons(wall,3,.1,true);assert.ok(wall[0].embers.every(p=>!p.visible));
 const board={content,lift:new T.Group(),glow:new T.Group()};batchBuiltDomain(a,board);wall.forEach(p=>p.root.traverse(o=>assert.ok(!board.batchedSources.includes(o))));values.fill(0);syncWallBeacons(wall,values);assert.ok(wall.every(p=>!p.fire.visible));
});
