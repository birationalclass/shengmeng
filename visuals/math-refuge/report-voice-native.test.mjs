import test from 'node:test';import assert from 'node:assert/strict';
import {createReportVoice} from './report-voice.js';
class NativeMedia extends EventTarget{
 static HAVE_ENOUGH_DATA=4;readyState=0;currentTime=0;paused=true;rate=1;rateWrites=[];plays=[];
 get playbackRate(){return this.rate;}set playbackRate(value){this.rateWrites.push({value,ready:this.readyState});this.rate=value;}
 pause(){this.paused=true;}load(){this.readyState=0;this.currentTime=0;}removeAttribute(){}
 metadata(){this.readyState=1;this.dispatchEvent(new Event('loadedmetadata'));}canPlay(){this.readyState=4;this.dispatchEvent(new Event('canplaythrough'));}
 async play(){assert.equal(this.readyState,4);this.plays.push({time:this.currentTime,rate:this.rate});this.paused=false;this.dispatchEvent(new Event('playing'));}
}
globalThis.HTMLMediaElement=NativeMedia;
const tick=()=>new Promise(r=>setTimeout(r,0));
function fixture(){const made=[],manifest={duration:20,policy:{audioTransport:'mp3-predecode-pcm',defaultPlaybackRate:.85,thinkingUsesRealSeconds:true},chapters:[{src:'first.mp3',page:0,start:0,duration:10},{src:'second.mp3',page:1,start:10,duration:10}],boards:[{page:0,start:0,end:10},{page:1,start:10,end:20}]},voice=createReportVoice({minimumBoardReview:false,baseURL:'https://refuge.test/',fetcher:async src=>src.endsWith('.json')?Response.json(manifest):new Response(new Uint8Array([82,73,70,70,4,0,0,0,87,65,86,69]),{headers:{'content-type':'audio/wav'}}),makeAudio:()=>{const a=new NativeMedia();made.push(a);return a;},makeURL:()=> 'blob:'+Math.random(),revokeURL(){}});return{voice,made,report:{id:'classroom',kind:'classroom',narration:{manifest:'narration.json'}}};}
test('PCM transport applies the rate only after readiness and reuses the player at the next onset',async()=>{
 const h=fixture(),selection=h.voice.select(h.report);await tick();const a=h.made[0];h.voice.update();h.voice.setRate(.85);assert.equal(a.rateWrites.length,0);a.metadata();await selection;const play=h.voice.toggle();await tick();assert(a.paused);assert.equal(a.rateWrites.length,0);a.canPlay();await play;assert.deepEqual(a.plays[0],{time:0,rate:.85});
 a.currentTime=8;const next=h.voice.seek(10);await tick();assert.equal(h.made.length,1);assert.equal(a.currentTime,0);a.metadata();await next;const resume=h.voice.toggle();await tick();a.canPlay();await resume;assert.equal(a.plays.at(-1).time,0);assert(a.rateWrites.every(r=>r.ready===4));assert.equal(h.voice.mediaState.elementsCreated,1);h.voice.dispose();
});
test('manual pause during priming and rapid source replacement cannot cause a stale restart',async()=>{
 const h=fixture(),selection=h.voice.select(h.report);await tick();const a=h.made[0];a.metadata();await selection;const play=h.voice.toggle();await tick();h.voice.pause();a.canPlay();await play;assert.equal(a.plays.length,0);
 const first=h.voice.seek(10),second=h.voice.seek(0);await tick();a.metadata();await Promise.all([first,second]);assert.equal(a.currentTime,0);assert(a.paused);assert.equal(h.made.length,1);h.voice.dispose();
});
