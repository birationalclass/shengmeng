import test from 'node:test';
import assert from 'node:assert/strict';
import {birthFrequency} from './challenge-audio.mjs';
test('the same element order always has the same pitch across calls',()=>{for(const n of [1,2,3,4,5,6,7]){const expected=birthFrequency(n);for(let i=0;i<20;i++)assert.equal(birthFrequency(n),expected);}});
test('orders used by campaign groups have distinct ascending musical pitches',()=>{const notes=[1,2,3,4,5,6,7].map(birthFrequency);assert.equal(new Set(notes).size,7);for(let i=1;i<notes.length;i++)assert.ok(notes[i]>notes[i-1]);assert.ok(notes[0]>=260&&notes.at(-1)<1000);});
test('invalid or extreme orders cannot produce inaudible or nonfinite values',()=>{for(const n of [undefined,null,0,-1,Infinity,NaN,1.5,1000000])assert.ok(birthFrequency(n)>=260&&birthFrequency(n)<2000);});
