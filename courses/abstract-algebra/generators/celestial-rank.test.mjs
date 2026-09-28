import test from 'node:test';
import assert from 'node:assert/strict';
import {groups} from './model.mjs';
import {elementOrder,celestialRank} from './celestial-rank.mjs';
test('element orders match known cyclic and permutation distributions',()=>{
 assert.deepEqual(groups.C4.labels.map((_,i)=>elementOrder(groups.C4,i)),[1,4,2,4]);
 const counts={};groups.S5.labels.forEach((_,i)=>{const n=elementOrder(groups.S5,i);counts[n]=(counts[n]||0)+1;});
 assert.deepEqual(counts,{1:1,2:25,3:20,4:30,5:24,6:20});
});
test('exactly one black hole per group and decreasing rank size with order',()=>{
 for(const g of Object.values(groups)){
  const orders=g.labels.map((_,i)=>elementOrder(g,i));
  assert.equal(orders.filter(n=>n===1).length,1);assert.equal(orders[g.e],1);
  for(const n of orders)assert.equal(g.table.length%n,0);
 }
 for(let n=1;n<120;n++)assert.ok(celestialRank(n).scale>=celestialRank(n+1).scale);
});
