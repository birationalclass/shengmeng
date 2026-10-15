import test from 'node:test';import assert from 'node:assert/strict';
import {REFERENCE_ICON_PATHS,referenceIconStrokePaths} from './classroom-metadata.js';
test('each disconnected bulb component is a separate pen stroke',()=>{
 const strokes=referenceIconStrokePaths('exercise');assert.equal(strokes.length,8);
 assert(strokes.every(d=>(d.match(/M/g)||[]).length===1));
 assert(strokes.includes('M9 18h6'));assert(strokes.includes('M9.5 21h5'));
 assert(strokes.some(d=>d.startsWith('M8.5 15.5')));
});
test('splitting moves preserves all native SVG geometry and other homepage icons',()=>{
 for(const kind of Object.keys(REFERENCE_ICON_PATHS))assert.equal(referenceIconStrokePaths(kind).join(''),REFERENCE_ICON_PATHS[kind].join(''));
 for(const kind of ['textbook','extension'])assert.deepEqual(referenceIconStrokePaths(kind),REFERENCE_ICON_PATHS[kind]);
});
