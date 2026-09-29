import test from 'node:test';
import assert from 'node:assert/strict';
import {createBirthMelody} from './challenge-audio.mjs';
test('births form bounded, varied phrases without immediate repetition or large leaps',()=>{
 let seed=71;const note=createBirthMelody(()=>{seed=seed*16807%2147483647;return(seed-1)/2147483646;}),heard=[];
 for(let i=0;i<240;i++){const hz=note();assert.ok(hz>=392&&hz<=784);if(heard.length){const before=heard.at(-1);assert.notEqual(hz,before);assert.ok(Math.abs(12*Math.log2(hz/before))<=5.01);}heard.push(hz);}assert.ok(new Set(heard).size>=5);
});
test('phrase stays in range even when repeatedly choosing either edge',()=>{for(const random of [()=>0,()=>.999999]){const note=createBirthMelody();const edge=createBirthMelody(random);for(let i=0;i<100;i++)assert.ok(Number.isFinite(edge()));assert.ok(Number.isFinite(note()));}});
