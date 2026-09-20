import test from 'node:test';
import assert from 'node:assert/strict';
import {skatingPose,installIceSkaters,updateIceSkaters} from '../ice-skaters.mjs';
import * as T from '../../3d/vendor/three.module.js';
import {AtlasScene} from '../../test-module/scene.mjs';
test('skaters stay outside the board and apart throughout their cycle',()=>{for(let t=0;t<400;t+=.05){const p=[0,1].map(i=>skatingPose(t,i));for(const s of p){assert.ok(Math.abs(s.x)>6.0||Math.abs(s.z)>6.0);assert.ok(Math.hypot(s.x,s.z)<9.3);assert.ok(Object.values(s).every(v=>typeof v==='boolean'||Number.isFinite(v)));}assert.ok(Math.hypot(p[0].x-p[1].x,p[0].z-p[1].z)>17);}});
test('two figures move, leave trails, and reduce-motion freezes the scene',()=>{const a=Object.create(AtlasScene.prototype);a.materials={};const parent=new T.Group();installIceSkaters(a,parent);assert.equal(a.iceSkaters.length,2);const before=a.iceSkaters.map(s=>s.root.position.clone());updateIceSkaters(a.iceSkaters,10,false);a.iceSkaters.forEach((s,i)=>{assert(s.root.position.distanceTo(before[i])>2);assert(s.trail.visible);});updateIceSkaters(a.iceSkaters,200,true);a.iceSkaters.forEach((s,i)=>{assert(s.root.position.distanceTo(before[i])<1e-9);assert(!s.trail.visible);});});
