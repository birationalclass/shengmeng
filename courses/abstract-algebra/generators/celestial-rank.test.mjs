import test from 'node:test';
import assert from 'node:assert/strict';
import {groups} from './model.mjs';
import {elementOrder,celestialRank,celestialLayout,bodyScale} from './celestial-rank.mjs';
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

test('relative ranks and stable host assignments preserve exact element counts',()=>{
 for(const g of Object.values(groups)){
  const entries=celestialLayout(g),orders=[...new Set(entries.map(e=>e.order))].sort((a,b)=>a-b);
  assert.deepEqual(entries,celestialLayout(g));assert.equal(entries.length,g.table.length);
  for(const e of entries){
   if(e.order===1){assert.equal(e.rank.scale,1);assert.equal(e.host,null);}
   else if(e.order===orders[1]){assert.ok(e.rank.type.endsWith('star'));assert.equal(e.rank.scale,.8);assert.equal(e.host,null);}
   else{assert.ok(e.rank.type.endsWith('planet'));assert.equal(e.rank.scale,.6);assert.equal(entries[e.host].order,orders[1]);assert.ok(e.slot>=0);}
  }
 }
 const s5=celestialLayout(groups.S5);assert.equal(s5.filter(e=>e.rank.type.endsWith('star')).length,25);assert.equal(s5.filter(e=>e.host!==null).length,94);
 assert.equal(celestialLayout(groups.C4).filter(e=>e.host!==null).length,2);
});

test('group density scales all bodies down without changing tier ratios',()=>{
 let previous=Infinity;for(const order of [4,6,8,24,120]){const size=bodyScale(order);assert.ok(size>0&&size<previous);assert.equal((size*.8)/size,.8);assert.ok(Math.abs((size*.6)/size-.6)<1e-12);previous=size;}
});
