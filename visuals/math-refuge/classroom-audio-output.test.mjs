import test from 'node:test';import assert from 'node:assert/strict';
import {primeClassroomAudio,classroomAudioOutputState} from './classroom-audio-output.js';
class Media extends EventTarget{static HAVE_ENOUGH_DATA=4;readyState=1;}
globalThis.HTMLMediaElement=Media;
test('native PCM waits for full playable readiness, then uses no live output graph',async()=>{
 const a=new Media();let done=false;const job=primeClassroomAudio(a).then(()=>done=true);await Promise.resolve();assert(!done);a.readyState=4;a.dispatchEvent(new Event('canplaythrough'));await job;assert(done);assert(a.preservesPitch);assert.equal(classroomAudioOutputState().contextsCreated,0);
});
test('source replacement cancels a native preparation without priming another source',async()=>{
 const a=new Media(),c=new AbortController(),job=primeClassroomAudio(a,{signal:c.signal});c.abort();await assert.rejects(job,{name:'AbortError'});a.readyState=4;a.dispatchEvent(new Event('canplaythrough'));await primeClassroomAudio(a);
});
