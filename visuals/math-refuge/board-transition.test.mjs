import test from 'node:test';import assert from 'node:assert/strict';
import {boardContentJump,boardFade} from './board-transition.js';
test('normal handwriting does not restart transitions; seeks and late content do',()=>{
 const before={page:2,progress:.4,available:true};
 assert.equal(boardContentJump(before,{...before,progress:.41}),false);
 assert.equal(boardContentJump(before,{...before,progress:.9}),true);
 assert.equal(boardContentJump(before,{...before,page:3}),true);
 assert.equal(boardContentJump({...before,available:false},before),true);
 assert.equal(boardContentJump(undefined,before),false);
});
test('fade is bounded, monotonic and settles to completely sharp current ink',()=>{
 assert.equal(boardFade(-1),0);assert.equal(boardFade(1),1);assert.equal(boardFade(2),1);
 let last=0;for(let i=0;i<=100;i++){const next=boardFade(i/100);assert(next>=last);last=next;}
});

import {advanceBoardQueue} from './board-transition.js';
test('next board waits until previous board fully finishes',()=>{
 const a={fadeAge:0,inkBlend:{value:0}},b={fadeAge:0,inkBlend:{value:0}},queue=[a,b];
 for(let i=0;i<6;i++){advanceBoardQueue(queue,.1);assert.equal(b.inkBlend.value,0);}
 advanceBoardQueue(queue,.1);assert.equal(a.inkBlend.value,1);assert.equal(b.inkBlend.value,0);
 advanceBoardQueue(queue,.1);assert(b.inkBlend.value>0);advanceBoardQueue(queue,0,true);assert.equal(queue.length,0);assert.equal(b.inkBlend.value,1);
});
