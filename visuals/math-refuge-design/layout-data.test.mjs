import assert from 'node:assert/strict';
import {snapshot,documentFor,validateDocument} from './layout-data.js';
const rows=[['01B','hall',0,0,-32,0,42,46],['01C','backup',0,0,-73,225,42,46]];
const doc=JSON.parse(JSON.stringify(documentFor(rows)));
assert.deepEqual(validateDocument(doc,rows),snapshot(rows));
for(const bad of [
 {...doc,units:'feet'},
 {...doc,buildings:[doc.buildings[0],doc.buildings[0]]},
 {...doc,buildings:[{...doc.buildings[0],east:10001},doc.buildings[1]]},
 {...doc,buildings:[{...doc.buildings[0],north:'123'},doc.buildings[1]]}
])assert.throws(()=>validateDocument(bad,rows));
assert.equal(rows[0][4],-32,'Serialization must not add another east shift');
console.log('PASS: JSON roundtrip, coordinate system, duplicate IDs, bounds, type validation, no cumulative shift');
