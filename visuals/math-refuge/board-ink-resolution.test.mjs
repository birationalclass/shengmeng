import test from 'node:test';import assert from 'node:assert/strict';import {boardInkScale} from './board-ink-resolution.js';
test('near desktop board gets extra texels while mobile and GPU limits remain respected',()=>{
 assert.equal(boardInkScale({width:2561,height:1441}),2);
 assert.equal(boardInkScale({base:.5,width:2561,height:1441}),.5);
 assert.equal(boardInkScale({width:10000,height:8000}),2);
 assert(boardInkScale({width:2561,height:1441,maxTextureSize:2048})*1536<=2048);
});
