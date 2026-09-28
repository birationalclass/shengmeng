import test from 'node:test';
import assert from 'node:assert/strict';
import {GROUP_KNOWLEDGE,normalizeLives,loseLife,knowledgeFor} from './group-knowledge.mjs';
test('twenty distinct lessons each have a statement, proof and practical hint',()=>{
 assert.equal(GROUP_KNOWLEDGE.length,20);assert.equal(new Set(GROUP_KNOWLEDGE.map(k=>k.title)).size,20);
 for(const k of GROUP_KNOWLEDGE)for(const field of ['statement','proof','hint'])assert.ok(k[field].length>10);
});
test('three failures exhaust a galaxy and require a fresh thirty second reading',()=>{
 let s=normalizeLives();for(const n of [2,1,0]){s=loseLife(s,()=>0);assert.equal(s.lives,n);}
 assert.equal(s.remaining,30);assert.equal(s.tip,0);assert.deepEqual(normalizeLives(JSON.parse(JSON.stringify(s))),s);
});
test('random lessons do not repeat until all twenty have been read',()=>{
 let s=normalizeLives(),seen=new Set();for(let i=0;i<20;i++){s=loseLife({...s,lives:1},()=>.47);assert.ok(!seen.has(s.tip));seen.add(s.tip);}
 s=loseLife({...s,lives:1},()=>.47);assert.equal(s.seen.length,1);assert.equal(seen.size,20);
});

test('lessons match their galaxy and start with its constructive proof',()=>{for(const key of ['S4','S5']){const s=loseLife({...normalizeLives(),lives:1},()=>0,key);assert.equal(s.tip,18);assert.ok(!knowledgeFor(key).some(k=>k.id===16||k.id===19));}assert.equal(loseLife({...normalizeLives(),lives:1},()=>0,'Q8').tip,16);assert.equal(loseLife({...normalizeLives(),lives:1},()=>0,'A5').tip,9);});
