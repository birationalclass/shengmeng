const fs = require('fs');
const vm = require('vm');
const assert = require('assert/strict');
class FakeAudio {
  static instances = [];
  constructor(src) { this.src=src; this.paused=true; this.volume=1; this.duration=177; this.readyState=4; this.seeking=false; this.listeners={}; this.playCalls=0; this.pauseCalls=0; this.seeks=0; this.time=0; FakeAudio.instances.push(this); }
  get currentTime(){ return this.time; }
  set currentTime(t){ this.time=t; this.seeks++; }
  play(){ this.playCalls++; if(this.reject) return Promise.reject(Object.assign(new Error('play'),{name:this.reject})); this.paused=false; if(this.pending) return new Promise(resolve=>{this.resolve=()=>{this.paused=false;resolve();};}); return Promise.resolve(); }
  pause(){ this.paused=true; this.pauseCalls++; }
  addEventListener(name,fn){ this.listeners[name]=fn; }
  removeEventListener(name){ delete this.listeners[name]; }
  removeAttribute(){} load(){} emit(name){ this.listeners[name]?.(); }
}
const document={hidden:false,listeners:{},addEventListener(k,f){this.listeners[k]=f;},removeEventListener(k){delete this.listeners[k];}};
const ctx={window:{},Audio:FakeAudio,document};
vm.runInNewContext(fs.readFileSync(require('node:path').join(__dirname,'../opening-galois-audio.js'),'utf8'),ctx);
const wait=()=>new Promise(r=>setImmediate(r));
const create=()=>{ const main=new FakeAudio('main');main.loop=true;let requests=0;const adapter=ctx.window.CourseOpeningGaloisAudio.create({mainAudio:main,requestMain(){requests++;if(adapter.status().suppressMain)return;return main.play();}});const score=FakeAudio.instances.at(-1);return{main,adapter,score,get requests(){return requests;}};};
const frame=(o,{active=true,t=0,direction=1,playing=true,enabled=true,dt=50}={})=>o.adapter.update({active,t,direction,playing,enabled,dt,volume:.72});
(async()=>{
 const o=create();
 for(let i=0;i<10;i++) frame(o,{active:false});
 assert.equal(o.score.playCalls,0,'no autoplay before unlock');
 await o.adapter.unlock();
 assert.equal(o.score.paused,true,'silent unlock immediately pauses score outside authorized playback state');
 await o.main.play();
 for(let i=0;i<65;i++){frame(o,{t:i*.05});if(!o.score.paused)o.score.time+=.05;await wait();}
 assert.equal(o.adapter.status().mix,1);assert.equal(o.main.paused,true);assert.equal(o.score.paused,false);assert(Math.abs(o.score.volume-.72)<1e-8);assert.equal(o.main.loop,true);
 assert(o.score.seeks<5,'must not seek every frame');
 o.score.readyState=1;frame(o,{t:3.25});assert.equal(o.main.paused,false,'buffering resumes main even after full handoff');o.score.readyState=4;for(let i=0;i<65;i++){frame(o,{t:3.25+i*.05});if(!o.score.paused)o.score.time+=.05;await wait();}
 const oldMainTime=o.main.currentTime=12;
 frame(o,{active:false,t:4});assert.equal(o.main.paused,false);assert.equal(o.main.currentTime,oldMainTime);assert.equal(o.adapter.status().suppressMain,false);
 for(let i=0;i<65;i++){frame(o,{active:false,t:4});await wait();}
 assert.equal(o.adapter.status().mix,0);assert.equal(o.score.paused,true);assert.equal(o.main.volume,.72);
 frame(o,{t:17});await wait();for(let i=0;i<65;i++){frame(o,{t:17+i*.05});if(!o.score.paused)o.score.time+=.05;await wait();}
 frame(o,{t:20,direction:-1});assert(o.score.paused&&o.main.paused);assert.equal(o.score.volume,0);
 frame(o,{t:13,direction:1});await wait();assert.equal(o.score.paused,false);assert.equal(o.score.currentTime,13);
 frame(o,{t:13,enabled:false});assert(o.score.paused&&o.main.paused);assert.equal(o.score.volume,0);assert.equal(o.main.volume,0);
 frame(o,{t:14,enabled:true});await wait();assert.equal(o.score.currentTime,14);
 document.hidden=true;document.listeners.visibilitychange();assert(o.score.paused&&o.main.paused);assert.equal(o.score.volume,0);
 document.hidden=false;frame(o,{t:14});await wait();assert.equal(o.score.paused,false);
 o.adapter.stop();assert(o.score.paused&&o.main.paused);assert.equal(o.main.volume,.72);assert.equal(o.score.currentTime,0);
 frame(o,{t:22});assert(o.score.paused&&o.main.paused);
 const late=create();late.score.pending=true;const pending=late.adapter.unlock();late.adapter.stop();late.score.resolve();await pending;assert.equal(late.score.paused,true,'late unlock completion stays stopped');
 const failed=create();failed.score.reject='NotSupportedError';await failed.adapter.unlock();frame(failed,{t:0});await wait();assert.equal(failed.adapter.status().failed,true);assert.equal(failed.main.paused,false);assert.equal(failed.main.volume,.72);assert.equal(failed.adapter.status().suppressMain,false);
 const denied=create();denied.score.reject='NotAllowedError';await denied.adapter.unlock();frame(denied,{t:0});await wait();assert.equal(denied.adapter.status().blocked,true);assert.equal(denied.main.paused,false);delete denied.score.reject;await denied.adapter.unlock();frame(denied,{t:1});await wait();assert.equal(denied.adapter.status().blocked,false);assert.equal(denied.score.paused,false);
 const metadata=create();metadata.score.emit('loadedmetadata');assert.equal((await metadata.adapter.ready).duration,177);
 console.log(JSON.stringify({pass:true,checks:['no_autoplay','silent_unlock','3s_crossfade','main_loop_preserved','main_time_preserved','no_frame_seeks','reverse_pause','forward_resync','mute','hidden','stop','late_promise','failure_fallback','gesture_retry','metadata_ready'],scoreSeeks:o.score.seeks},null,2));
})().catch(e=>{console.error(e);process.exit(1);});
