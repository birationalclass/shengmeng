import {test} from 'node:test';
import assert from 'node:assert/strict';
import {createReportVoice,narrationFrame,syncNarrationClock} from './report-voice.js';
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
