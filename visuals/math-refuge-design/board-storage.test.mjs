import test from 'node:test';
import assert from 'node:assert/strict';
import {BoardStorage,subtractRect} from './board-storage.js';
test('shaft opens fully before either lift direction and closes at both endpoints',()=>{
 const s=new BoardStorage(true);
 for(const target of [false,true]){
  let sawMove=false;
  for(let i=0;i<100;i++){
   const p=s.progress;s.update(.1,target);
   if(s.progress!==p){sawMove=true;assert.equal(s.lid,1);}
   if(s.lid<1)assert.ok(s.progress===0||s.progress===1);
  }
  assert.ok(sawMove);assert.equal(s.progress,Number(target));assert.equal(s.lid,0);assert.ok(s.ready);
 }
});
test('reversing a request cannot move through a partially closed lid',()=>{
 const s=new BoardStorage();
 for(let i=0;i<180;i++){
  const p=s.progress;s.update(.1,i<30||i>=70);
  if(s.progress!==p)assert.equal(s.lid,1);
 }
 assert.equal(s.progress,1);assert.equal(s.lid,0);
});
test('floor cut retains all area except shaft, including boundary-straddling cuts',()=>{
 for(const hole of [[3,7,2,8],[8,12,2,8],[-2,12,-2,12],[11,12,2,8]]){
  const cells=subtractRect([0,10,0,10],hole);
  const area=cells.reduce((s,[a,b,c,d])=>s+(b-a)*(d-c),0);
  const [a,b,c,d]=hole;const removed=Math.max(0,Math.min(10,b)-Math.max(0,a))*Math.max(0,Math.min(10,d)-Math.max(0,c));
  assert.equal(area,100-removed);
 }
});
