import test from 'node:test';import assert from 'node:assert/strict';import {verticalDestination as swipe} from './galaxy-swipe.mjs';
const base={dx:3,dy:80,index:1,count:9,passed:0,required:2};
test('portrait next preview requires every difficulty, previous remains available',()=>{assert.equal(swipe(base),'locked');assert.equal(swipe({...base,passed:1}),'locked');assert.equal(swipe({...base,passed:2}),2);assert.equal(swipe({...base,dy:-80}),0);});
test('ignore taps, diagonal drags and endpoints',()=>{assert.equal(swipe({...base,dy:20}),null);assert.equal(swipe({...base,dx:100}),null);assert.equal(swipe({...base,index:0,dy:-80}),null);assert.equal(swipe({...base,index:8,passed:2}),null);});
import {bindPortraitSwipe} from './galaxy-swipe.mjs';
test('touch gesture is blocked before completion, navigates after completion and cancels cleanly',()=>{
 const events={},calls=[];let passed=0;const prior=globalThis.document;globalThis.document={querySelector:()=>null};
 const host={innerWidth:390,innerHeight:844,addEventListener:(name,fn)=>events[name]=fn};
 try{bindPortraitSwipe({host,getState:()=>({...base,passed}),onSelect:i=>calls.push(i),onLocked:()=>calls.push('locked')});
 const down={isPrimary:true,pointerType:'touch',pointerId:4,clientX:100,clientY:200,target:{closest:()=>null}},up={pointerId:4,clientX:105,clientY:320};
 events.pointerdown(down);events.pointerup(up);assert.deepEqual(calls,['locked']);passed=2;
 events.pointerdown(down);events.pointerup(up);assert.deepEqual(calls,['locked',2]);
 events.pointerdown(down);events.pointercancel();events.pointerup(up);assert.equal(calls.length,2);
 events.pointerdown(down);events.pointerup({...up,clientY:100});assert.equal(calls.at(-1),0);
 }finally{globalThis.document=prior;}
});
