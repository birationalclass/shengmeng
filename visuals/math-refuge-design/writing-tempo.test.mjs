import test from 'node:test';
import assert from 'node:assert/strict';
import {writingPlan} from './chalk-motion.js';
const row=(scale,units=1)=>Object.assign([0,0,20*scale,30*scale],{strokePath:[[0,0],[10*scale,30*scale],[20*scale,0]],writeUnits:units});
test('character duration is independent of font size and travel distance',()=>{
 assert.equal(writingPlan([row(1)]).duration,writingPlan([row(5)]).duration);
 assert.equal(writingPlan([row(1),row(1)]).duration,2*writingPlan([row(1)]).duration);
 assert.equal(writingPlan([row(1,.5),row(2,.5)]).duration,writingPlan([row(1)]).duration);
});
