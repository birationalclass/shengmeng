import test from 'node:test';
import assert from 'node:assert/strict';
import {VILLA_PLAN as P,roomArea,villaFootprint} from './residence-plan.js';
test('villa room schedule partitions the 864 square metre courtyard ring without overlaps',()=>{
 assert.equal(P.rooms.reduce((n,r)=>n+roomArea(r),0),villaFootprint);
 for(const [i,r]of P.rooms.entries()){
  const[a,b,c,d]=r.bounds;assert(a>=-18&&b<=18&&c>=-14&&d<=14&&a<b&&c<d);
  assert(Math.min(b,6)<=Math.max(a,-6)||Math.min(d,6)<=Math.max(c,-6),'Open courtyard remains outdoors');
  for(const q of P.rooms.slice(i+1)){const[e,f,g,h]=q.bounds;assert(Math.min(b,f)<=Math.max(a,e)||Math.min(d,h)<=Math.max(c,g),r.id+' overlaps '+q.id);}
 }
});
test('villa roofs leave the court open and include its occupied room corners',()=>{
 for(const[x,z,w,d]of P.roofs)assert(Math.abs(x)>=6+w/2||Math.abs(z)>=6+d/2);
 for(const r of P.rooms){const[a,b,c,d]=r.bounds;for(const[x,z]of [[a+.01,c+.01],[b-.01,d-.01]])assert(P.roofs.some(([rx,rz,w,h])=>Math.abs(x-rx)<=w/2&&Math.abs(z-rz)<=h/2));}
 assert(P.corridor-P.wall>=1.7);assert(P.doorHeight<P.privateHeight);
});
