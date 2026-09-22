import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../../3d/vendor/three.module.js';
import {SudokuAtlas} from '../atlas.mjs';
function atlas(seconds=15){
 const a=Object.create(SudokuAtlas.prototype);Object.assign(a,{camera:new T.PerspectiveCamera(40,1,.65,900),currentTarget:new T.Vector3(),canvas:{dataset:{}},constructions:new Map(),built:new Set(),boards:Array.from({length:8},()=>({content:new T.Group()})),decorationSeconds:seconds,bridgeProgress:Array(7).fill(0),assembled:new Map()});
 a.assemble=(index,t)=>a.assembled.set(index,t);a.showBuilt=index=>a.built.add(index);return a;
}
function step(a,dt,reduced=false){a.updateConstruction(dt,reduced);a.updateSequence(dt,reduced);}
test('all eight boards unlock after rising while long scenery construction stays independent',()=>{
 for(let index=0;index<8;index++)for(const seconds of [5,15,45]){
  const a=atlas(seconds);let ready=0;a.arrive(index,()=>ready++);step(a,4.19);assert.equal(ready,0);step(a,.02);assert.equal(ready,1);assert.equal(a.sequence,null);assert.ok(a.constructions.has(index));assert.ok(!a.built.has(index));assert.ok(a.assembled.get(index)>=1.2);
  a.focus(-1);step(a,seconds+1);assert.ok(a.built.has(index));assert.equal(a.constructions.size,0);assert.equal(ready,1);
 }
});
test('early completion can cross to the next board while the former scenery keeps assembling',()=>{
 const a=atlas(45);let next=0;a.arrive(0,()=>{});step(a,4.21);a.cross(0,()=>{next++;a.arrive(1,()=>{});});step(a,8.6);assert.equal(next,1);assert.equal(a.sequence.index,1);assert.equal(a.constructions.size,2);step(a,4.21);assert.equal(a.sequence,null);assert.equal(a.constructions.size,2);step(a,50);assert.ok(a.built.has(0)&&a.built.has(1));
});
test('re-entering an unfinished region preserves its construction and reduced motion completes it',()=>{
 const a=atlas(45);a.arrive(7,()=>{});step(a,5);const job=a.constructions.get(7);let ready=0;a.arrive(7,()=>ready++);assert.equal(a.constructions.get(7),job);assert.equal(a.sequence.duration,2.8);step(a,2.8);assert.equal(ready,1);a.updateConstruction(0,true);assert.ok(a.built.has(7));assert.equal(a.constructions.size,0);
 const b=atlas();b.arrive(2,()=>ready++,true);assert.equal(ready,2);assert.equal(b.sequence,null);assert.ok(b.built.has(2));
});

test('background progress restoration leaves active construction and bridge movement intact',()=>{
 const a=atlas(45);a.setProgress=()=>{};a.updateBridges=()=>{};
 a.arrive(0,()=>{});step(a,4.21);const job=a.constructions.get(0);a.cross(0,()=>{});a.bridgeProgress[0]=.35;
 a.restore([2,3],{background:true});assert.equal(a.constructions.get(0),job);assert(!a.built.has(0));assert(a.built.has(1));assert.equal(a.bridgeProgress[0],.35);assert.equal(a.sequence.kind,'bridge');
});
