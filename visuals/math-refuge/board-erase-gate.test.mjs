import test from 'node:test';
import assert from 'node:assert/strict';
import {pendingEraseWork,boardWorkFrame} from './board-work.js';
const board={page:6,eraseStart:2.6,writeStart:40},done=new Set();
test('actual erasing gates writing even when the nominal time budget was sufficient',()=>{
 const job=pendingEraseWork(board,40.02,{page:6,duration:20,elapsed:17},done,'erasing');
 assert.equal(job.kind,'erase');assert.equal(job.elapsed,17);assert.equal(boardWorkFrame(job).phase,'erase');assert.equal(boardWorkFrame(job).writing,false);
});
test('final wipe and returning eraser both keep the writing gate closed',()=>{
 for(const state of ['erasing','returning']){const job=pendingEraseWork(board,40.1,{page:6,duration:20,elapsed:20},done,state);assert.ok(job);assert.equal(boardWorkFrame(job).progress,1);assert.equal(boardWorkFrame(job).writing,false);}
 assert.equal(pendingEraseWork(board,40.1,{page:6,duration:20,elapsed:20},done,'resting'),null);
});
test('slow frame crossing still gates actual work without replaying seeks or unrelated boards',()=>{
 assert.ok(pendingEraseWork(board,42,{page:6,duration:20,elapsed:15},done,'erasing'));
 for(const run of [null,{page:5,duration:20,elapsed:0}])assert.equal(pendingEraseWork(board,42,run,done,'erasing'),null);
 assert.equal(pendingEraseWork(board,39,{page:6,duration:20,elapsed:1},done,'erasing'),null);
 assert.equal(pendingEraseWork(board,42,{page:6,duration:20,elapsed:15},new Set(['erase:6']),'erasing'),null);
});
