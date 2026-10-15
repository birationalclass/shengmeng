import test from 'node:test';import assert from 'node:assert/strict';
import {BoardReview} from './board-review.js';import {narrationWork,boardWorkFrame} from './board-work.js';
test('a completed board remains for five wall seconds, including pause, without resetting on redraw',()=>{
 let time=100;const review=new BoardReview(()=>time);review.mark(2);time+=2;assert.equal(review.remaining(2),3);review.mark(2);time+=3.1;assert.equal(review.remaining(2),0);assert.equal(review.remaining(3),5);review.clear();assert.equal(review.remaining(2),5);
});
test('automatic transition waits only for the remaining reading time, after ink is complete',()=>{
 const plan={physicalTiming:true,unitsPerSecond:10,total:10,segments:[{start:0,end:10,mainLine:0}]},m={boards:[{page:0,start:0,writeStart:0,end:3}]};
 const work=narrationWork(m,2.99,2.97,plan,null,new Set(),4.2);assert.equal(work.kind,'review');assert.equal(work.duration,4.2);assert.deepEqual([boardWorkFrame(work).phase,boardWorkFrame(work).progress,boardWorkFrame(work).writing],['hold',1,false]);
 assert.equal(narrationWork(m,2.99,2.97,plan,null,new Set(),0),null);assert.equal(narrationWork(m,2.99,2.97,plan,null,new Set([work.key]),4.2),null);
});
