import test from 'node:test';import assert from 'node:assert/strict';
import{normalizeErasingSpeed,loadErasingSpeed,saveErasingSpeed,eraseSilenceTarget,ERASING_SPEED_KEY}from'./board-erasing-speed.js';
import{LectureClock}from'./lecture-state.js';
test('fresh browser defaults to 2x; invalid storage cannot break the board',()=>{
 for(const v of [null,undefined,'',0,-2,'bad',Infinity])assert.equal(normalizeErasingSpeed(v),2);
 assert.equal(normalizeErasingSpeed(.1),.5);assert.equal(normalizeErasingSpeed(20),4);
 assert.equal(loadErasingSpeed({getItem(){throw Error('blocked')}}),2);
 const data=new Map(),storage={getItem:k=>data.get(k),setItem:(k,v)=>data.set(k,v)};
 assert.equal(saveErasingSpeed(3,storage),3);assert.equal(data.get(ERASING_SPEED_KEY),'3');assert.equal(loadErasingSpeed(storage),3);
});
test('ordinary erase clock scales after the frame cap; writing and holds keep their timing',()=>{
 for(const rate of [.5,1,2,4]){const c=new LectureClock(8);c.seek(6);c.phase='erase';c.elapsed=0;c.update(.1,rate);assert.equal(c.elapsed,.1*rate);}
 const c=new LectureClock(8);c.seek(6);c.phase='hold';c.elapsed=0;c.update(.1);assert.equal(c.elapsed,.1);assert(c.duration>=10);
});
const board={page:6,eraseStart:2.6,writeStart:40,lineCues:[{audioStart:42}]},run={page:6,elapsed:20,duration:20},manifest={paragraphs:[{page:6,start:42,end:47}]};
test('finishing the wipe and return skips only remaining pre-writing silence',()=>{assert.equal(eraseSilenceTarget(manifest,board,25,run,'resting'),40);});
test('returning, unfinished, first-use, speech and unannotated media are never skipped',()=>{
 assert.equal(eraseSilenceTarget(manifest,board,25,run,'returning'),null);
 assert.equal(eraseSilenceTarget(manifest,board,25,{...run,elapsed:19},'resting'),null);
 assert.equal(eraseSilenceTarget(manifest,{...board,page:1},25,{...run,page:1},'resting'),null);
 assert.equal(eraseSilenceTarget({paragraphs:[{page:6,start:24,end:31}]},board,25,run,'resting'),null);
 assert.equal(eraseSilenceTarget({},board,25,run,'resting'),null);
 assert.equal(eraseSilenceTarget(manifest,board,41,run,'resting'),null);
});
