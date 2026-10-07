import {test} from 'node:test';
import assert from 'node:assert/strict';
import {createReportVoice,narrationFrame,syncNarrationClock,rowNarrationProgress,reportVoicePresentation,reportVoiceIconPosition} from './report-voice.js';
import {LectureClock,boardSlot} from './lecture-state.js';
class FakeAudio extends EventTarget{
 currentTime=0;paused=true;
 pause(){this.paused=true;}
 async play(){this.paused=false;this.dispatchEvent(new Event('playing'));}
}
const manifest={duration:20,chapters:[{src:'a.mp3',start:0,duration:10,bytes:4},{src:'b.mp3',start:10,duration:10,bytes:4}],boards:[{page:0,start:0,eraseStart:0,writeStart:0,writeEnd:5,end:10},{page:1,start:10,eraseStart:12,writeStart:12,writeEnd:16,end:20}]};
const report={id:'ye',narration:{manifest:'narration.json'}};
function harness(extra={}){
 const calls=[],states=[],audios=[],revoked=[];
 const voice=createReportVoice({baseURL:'https://example.com/hall/',fetcher:async src=>{calls.push(src);return src.endsWith('.json')?Response.json(manifest):new Response(new Uint8Array([1,2,3,4]),{headers:{'content-length':'4'}});},makeAudio:()=>{const a=new FakeAudio();audios.push(a);return a;},makeURL:()=> 'blob:'+Math.random(),revokeURL:u=>revoked.push(u),onChange:s=>states.push(s),...extra});
 return{voice,calls,states,audios,revoked};
}
const tick=()=>new Promise(r=>setTimeout(r,0));
test('no audio requests at startup or for reports without narration',async()=>{const h=harness();assert.equal(h.calls.length,0);await h.voice.select({id:'hu'});assert.equal(h.calls.length,0);h.voice.dispose();});
test('select loads only directory and first chapter, shows measured bytes, never autoplays',async()=>{const h=harness();await h.voice.select(report);assert.equal(h.calls.length,2);assert.equal(h.audios[0].paused,true);assert.equal(h.voice.state.phase,'ready');assert(h.states.some(s=>s.progress===.99));await h.voice.toggle();h.audios[0].currentTime=3.25;h.voice.update();assert.equal(h.voice.state.time,3.25);h.voice.pause();assert.equal(h.voice.state.phase,'paused');h.voice.dispose();assert.equal(h.revoked.length,1);});
test('chapter transitions continue sequentially and use absolute audio time',async()=>{const h=harness();await h.voice.select(report);await h.voice.toggle();h.voice.update();await tick();assert.equal(h.calls.length,3);h.audios[0].dispatchEvent(new Event('ended'));await tick();assert.equal(h.voice.state.chapter,1);assert.equal(h.voice.state.phase,'playing');h.audios[1].currentTime=2;h.voice.update();assert.equal(h.voice.state.time,12);h.audios[1].dispatchEvent(new Event('ended'));assert.equal(h.voice.state.phase,'ended');assert.equal(h.voice.state.time,20);h.voice.dispose();});
test('seek pauses and fetches only the selected chapter; resume preserves position',async()=>{const h=harness();await h.voice.select(report);await h.voice.seek(14);assert.equal(h.voice.state.phase,'paused');assert.equal(h.audios.at(-1).currentTime,4);await h.voice.toggle();h.voice.update();assert.equal(h.voice.state.time,14);h.voice.dispose();});
test('changing reports rejects stale directory data and releases existing audio',async()=>{let release;const h=harness({fetcher:()=>new Promise(r=>release=r)});const job=h.voice.select(report);await h.voice.select({id:'hu'});release(Response.json(manifest));await job;assert.equal(h.voice.state.phase,'idle');assert.equal(h.audios.length,0);h.voice.dispose();});
test('pause during a delayed play promise cannot restart playback',async()=>{let release;const a=new FakeAudio();a.play=()=>new Promise(r=>release=r);const h=harness({makeAudio:()=>a});await h.voice.select(report);const job=h.voice.toggle();h.voice.pause();release();await job;assert.equal(a.paused,true);assert.notEqual(h.voice.state.phase,'playing');h.voice.dispose();});
test('failed fetch stays error rather than reporting completion',async()=>{const h=harness({fetcher:async()=>new Response('',{status:404})});assert.equal(await h.voice.select(report),false);assert.equal(h.voice.state.phase,'error');h.voice.dispose();});
test('board timeline writes, pauses, lifts, erases, and reconstructs no future ink',()=>{
 const boards=Array.from({length:8},(_,page)=>({page,start:page*20,eraseStart:page*20+2,writeStart:page*20+(page>=6?8:2),writeEnd:page*20+14,end:page*20+20}));
 const m={boards,duration:160},clock=new LectureClock(8);
 let f=narrationFrame(m,125);assert.equal(f.page,6);assert.equal(f.phase,'erase');syncNarrationClock(clock,f,boardSlot);assert.equal(clock.slots[boardSlot(6)].page,0);assert(clock.slots.every(s=>s.page<6));
 f=narrationFrame(m,131);syncNarrationClock(clock,f,boardSlot);assert.equal(f.phase,'write');assert.equal(clock.slots[boardSlot(6)].page,6);assert.equal(clock.slots[boardSlot(6)].progress,.5);assert(clock.slots.every(s=>s.page<=6));
 f=narrationFrame(m,160);syncNarrationClock(clock,f,boardSlot);assert(clock.ended);assert.equal(clock.page,7);
});


test('missing board assets suspend the speech clock and resume only after readiness',async()=>{
 const h=harness();await h.voice.select(report);await h.voice.toggle();h.audios[0].currentTime=3;
 let ready;const waiting=h.voice.suspendUntil(new Promise(r=>ready=r));
 assert(h.audios[0].paused);assert.equal(h.voice.state.phase,'preparing');assert.equal(h.voice.state.time,3);
 ready();await waiting;assert.equal(h.voice.state.phase,'playing');assert.equal(h.audios[0].currentTime,3);h.voice.dispose();
});
test('pausing while a board loads prevents both automatic resume and a stale load error',async()=>{
 for(const fails of [false,true]){
  const h=harness();await h.voice.select(report);await h.voice.toggle();let resolve,reject;
  const waiting=h.voice.suspendUntil(new Promise((r,e)=>{resolve=r;reject=e;}));h.voice.pause();
  if(fails)reject(Error('late failure'));else resolve();await waiting;
  assert.equal(h.voice.state.phase,'paused');assert(h.audios[0].paused);h.voice.dispose();
 }
});


test('per-line audio uses measured ink costs, holds for explanation, and seeks without future ink',()=>{
 const plan={total:100,segments:[{start:0,end:10,mainLine:0},{start:10,end:20,mainLine:1},{start:20,end:70,mainLine:1},{start:70,end:100,mainLine:2}]};
 const cues=[{row:0,writeStart:0,writeEnd:2},{row:1,writeStart:4,writeEnd:10},{row:2,writeStart:15,writeEnd:20}];
 assert.equal(rowNarrationProgress(cues,3,plan),.1,'explanation holds the heading');
 assert.equal(rowNarrationProgress(cues,7,plan),.4,'half of the long line is half its own stroke cost');
 assert.equal(rowNarrationProgress(cues,14,plan),.7,'next line stays blank');
 assert.equal(rowNarrationProgress(cues,17.5,plan),.85);
 assert.equal(rowNarrationProgress(cues,4,plan),.1,'seek backwards reconstructs exact row boundary');
 const m={duration:25,boards:[{page:0,start:0,eraseStart:0,writeStart:0,writeEnd:20,end:25,lineCues:cues}]};
 const f=narrationFrame(m,14,plan),clock=new LectureClock(1);syncNarrationClock(clock,f,boardSlot);
 assert.equal(clock.progress,.7);assert.equal(clock.slots[0].progress,.7);assert.equal(f.writing,false);assert.equal(narrationFrame(m,7,plan).writing,true);
 assert.equal(narrationFrame(m,21,plan).phase,'hold');
 assert.throws(()=>rowNarrationProgress([{row:3,writeStart:0,writeEnd:1}],0,plan),/no visible ink/);
});


test('formal hall shows audio readiness, measured loading, pause, and retry',()=>{
 const state={phase:'loading',progress:.42,time:0,duration:3314.795,error:''};
 assert.equal(reportVoicePresentation(state).busy,true);assert.match(reportVoicePresentation(state).message,/42%/);
 assert.equal(reportVoicePresentation({...state,phase:'ready'}).busy,false);assert.match(reportVoicePresentation({...state,phase:'ready'}).message,/55:14/);
 for(const phase of ['playing','buffering','preparing'])assert.equal(reportVoicePresentation({...state,phase}).buttonLabel,'暂停报告');
 assert.equal(reportVoicePresentation({...state,phase:'error'}).buttonLabel,'重试报告语音');
 assert.equal(reportVoicePresentation({...state,phase:'idle'}).message,'');
});
test('play icon sits below the board beside the language target without overlap',async()=>{
 const {BOARD_LAYOUT}=await import('./lecture-state.js');
 for(const column of [0,1,2]){
  const p=reportVoiceIconPosition(column),center=22.4+5.6*column;
  assert(p.y+.48/2<BOARD_LAYOUT.low-BOARD_LAYOUT.height/2);
  assert(p.x-.48/2>center+2.2/2,'play hit target must not overlap the language hit target');
  assert(p.x+.48/2<center+BOARD_LAYOUT.width/2);
  assert(p.z>-11.332,'icon stays on the front face of smart glass');
 }
});


test('leaving temporarily pauses at the same audio position and returning resumes',async()=>{
 const h=harness();await h.voice.select(report);await h.voice.toggle();h.audios[0].currentTime=3.25;
 await h.voice.setContextActive(false);assert(h.audios[0].paused);assert.equal(h.voice.state.phase,'away');assert(h.voice.state.temporaryPause);assert.equal(h.voice.state.time,3.25);
 await h.voice.setContextActive(false);assert.equal(h.voice.state.time,3.25);
 await h.voice.setContextActive(true);assert.equal(h.voice.state.phase,'playing');assert.equal(h.audios[0].currentTime,3.25);assert(!h.voice.state.temporaryPause);h.voice.dispose();
});
test('manual pause, report changes, readiness, and ended reports never resume on entry',async()=>{
 const h=harness();await h.voice.select(report);await h.voice.setContextActive(false);await h.voice.setContextActive(true);assert.equal(h.voice.state.phase,'ready');
 await h.voice.toggle();h.voice.pause();await h.voice.setContextActive(false);await h.voice.setContextActive(true);assert.equal(h.voice.state.phase,'paused');
 await h.voice.toggle();await h.voice.setContextActive(false);h.voice.pause();await h.voice.setContextActive(true);assert.equal(h.voice.state.phase,'paused');
 await h.voice.toggle();await h.voice.setContextActive(false);await h.voice.select({id:'hu'});await h.voice.setContextActive(true);assert.equal(h.voice.state.phase,'idle');
 await h.voice.select(report);await h.voice.seek(14);await h.voice.toggle();h.audios.at(-1).dispatchEvent(new Event('ended'));await h.voice.setContextActive(false);await h.voice.setContextActive(true);assert.equal(h.voice.state.phase,'ended');h.voice.dispose();
});
test('a chapter finishing its download outside stays suspended until re-entry',async()=>{
 let complete;const h=harness({fetcher:async src=>src.endsWith('.json')?Response.json(manifest):src.endsWith('b.mp3')?new Promise(r=>complete=r):new Response(new Uint8Array([1,2,3,4]))});
 await h.voice.select(report);await h.voice.toggle();h.audios[0].dispatchEvent(new Event('ended'));await tick();
 await h.voice.setContextActive(false);complete(new Response(new Uint8Array([1,2,3,4])));await tick();assert.equal(h.voice.state.phase,'away');assert(h.audios.at(-1).paused);
 await h.voice.setContextActive(true);assert.equal(h.voice.state.phase,'playing');assert.equal(h.voice.state.chapter,1);h.voice.dispose();
});
