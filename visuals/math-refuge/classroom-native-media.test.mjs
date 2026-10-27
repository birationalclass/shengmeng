import test from 'node:test';import assert from 'node:assert/strict';
import {createClassroomNativeMedia} from './classroom-native-media.js';
class Media extends EventTarget{readyState=0;currentTime=0;loads=0;paused=true;pause(){this.paused=true;}load(){this.loads++;this.readyState=0;this.currentTime=0;}metadata(){this.readyState=1;this.dispatchEvent(new Event('loadedmetadata'));}}
test('native classroom keeps one player across boards and explicitly resets its position',async()=>{
 const made=[],pool=createClassroomNativeMedia(()=>{const a=new Media();made.push(a);return a;});const first=pool.attach('blob:first');assert.equal(made.length,1);assert.equal(first.audio.loads,1);first.audio.metadata();assert(await first.ready);first.audio.currentTime=19;
 const second=pool.attach('blob:second');assert.equal(second.audio,first.audio);assert.equal(second.audio.currentTime,0);assert(first.signal.aborted);second.audio.metadata();assert(await second.ready);assert.equal(second.audio.currentTime,0);assert.equal(pool.state.elementsCreated,1);pool.dispose();
});
test('replacing a source cancels its metadata wait and stale metadata cannot rewind a seek',async()=>{
 const pool=createClassroomNativeMedia(()=>new Media()),first=pool.attach('blob:old',{at:8}),second=pool.attach('blob:new',{at:2});assert.equal(await first.ready,false);second.audio.metadata();assert(await second.ready);assert.equal(second.audio.currentTime,2);second.audio.currentTime=4;second.audio.metadata();assert.equal(second.audio.currentTime,4);pool.clear();assert(!pool.state.active);
});
