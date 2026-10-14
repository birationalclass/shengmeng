import test from 'node:test';import assert from 'node:assert/strict';
import {writingSchedule,scheduledWriting,narrationWork,boardWorkFrame,settledBoardFrame} from './board-work.js';
import {narrationFrame,createReportVoice,VoiceIconMotion} from './report-voice.js';
const plan={physicalTiming:true,unitsPerSecond:10,total:100,segments:[{start:0,end:50,mainLine:0},{start:50,end:100,mainLine:1}]};
const board={page:0,start:0,eraseStart:0,writeStart:0,writeEnd:4,end:20,lineCues:[{row:0,writeStart:0,writeEnd:2},{row:1,writeStart:3,writeEnd:4}]};
test('natural handwriting continues through short cue boundaries without a pause or an ink jump',()=>{
 const schedule=writingSchedule(board,plan);assert.deepEqual(schedule.entries.map(e=>[e.start,e.end]),[[0,5],[5,10]]);
 const manifest={duration:20,boards:[board]};let previous=0;
 for(let t=.1;t<10;t+=.1){const frame=narrationFrame(manifest,t,plan);assert(frame.progress>=previous);assert(frame.progress-previous<.011);assert.equal(frame.phase,'write');assert(frame.writing);assert.equal(narrationWork(manifest,t,t-.1,plan,null,new Set()),null);previous=frame.progress;}
 assert.equal(narrationFrame(manifest,11,plan).progress,1);
});
test('only a whole-board overrun holds once, retaining the exact unfinished ink',()=>{
 const b={...board,end:6},m={duration:10,boards:[b]};assert.equal(narrationWork(m,2.01,1.99,plan,null,new Set()),null);
 const work=narrationWork(m,5.76,5.74,plan,null,new Set());assert(work);assert.equal(work.at,5.75);assert.equal(boardWorkFrame(work).progress,scheduledWriting(writingSchedule(b,plan),5.75).progress);
 assert.equal(narrationWork(m,5.76,5.74,plan,null,new Set([work.key])),null);
});
test('completed board ink stays complete when audio resumes from an overrun hold',()=>{
 const m={duration:10,boards:[{...board,end:6}]},completed=new Set(['write:0:end']);
 for(const t of [5.75,5.85,5.99]){const frame=settledBoardFrame(narrationFrame(m,t,plan),completed);assert.equal(frame.progress,1);assert.equal(frame.writing,false);assert.equal(frame.phase,'hold');}
 assert(narrationFrame(m,5.85,plan).progress<1,'the unfinished natural schedule must not rewind already completed ink');
});
test('physical preparation keeps the pause icon active and manual pause turns it into play',()=>{
 const motion=new VoiceIconMotion();let frame;
 for(let i=0;i<30;i++)frame=motion.update({phase:'preparing',transportPlaying:true,started:true,progress:1,chapter:0},.1);
 assert.equal(frame.kind,'pause');for(let i=0;i<10;i++)frame=motion.update({phase:'paused',transportPlaying:false,started:true,progress:1,chapter:0},.1);assert.equal(frame.kind,'play');
});
test('explicit pause stores elapsed silence and resumes at that same audio position',async()=>{
 const manifest={duration:10,chapters:[{start:0,duration:10,src:'one.mp3'}],boards:[{...board,end:10}],paragraphs:[{start:0,end:1},{start:5,end:6}]};
 const audio=new class extends EventTarget{currentTime=0;paused=true;pause(){this.paused=true;}async play(){this.paused=false;this.dispatchEvent(new Event('playing'));}};
 const voice=createReportVoice({baseURL:'https://example.com/',fetcher:async url=>url.endsWith('.json')?Response.json(manifest):new Response(new Uint8Array([1])),makeAudio:()=>audio,makeURL:()=> 'blob:test',revokeURL:()=>{}});
 await voice.select({id:'test',narration:{manifest:'test.json'}});await voice.toggle();audio.currentTime=3;voice.pause();assert.equal(voice.state.time,3);assert(!voice.transportPlaying);
 await voice.toggle();assert(voice.transportPlaying);assert.equal(audio.currentTime,3,'two seconds of silence remain; do not replay the full four-second gap');voice.dispose();
});
test('physical waiting retains play intent, but a real pause freezes it until an explicit resume',async()=>{
 const m={duration:10,chapters:[{start:0,duration:10,src:'one.mp3'}],boards:[board]},audio=new class extends EventTarget{currentTime=0;pause(){}async play(){this.dispatchEvent(new Event('playing'));}};
 const voice=createReportVoice({baseURL:'https://example.com/',fetcher:async url=>url.endsWith('.json')?Response.json(m):new Response(new Uint8Array([1])),makeAudio:()=>audio,makeURL:()=> 'blob:test',revokeURL:()=>{}});
 await voice.select({id:'test',narration:{manifest:'test.json'}});await voice.toggle();let done;const job=voice.holdForBoard(new Promise(r=>done=r),2);assert(voice.transportPlaying);voice.pause();assert(!voice.transportPlaying);assert(voice.boardHeld);await voice.toggle();assert(voice.transportPlaying);done();await job;assert.equal(voice.state.phase,'playing');voice.dispose();
});
