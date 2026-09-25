import test from 'node:test';
import assert from 'node:assert/strict';
import {bindRenderActivity} from './render-activity.js';
function harness({focused=true,hidden=false}={}){
 const target=()=>{const events=new Map();return {addEventListener(k,f){if(!events.has(k))events.set(k,new Set());events.get(k).add(f);},removeEventListener(k,f){events.get(k)?.delete(f);},emit(k){for(const f of events.get(k)||[])f();}};};
 const win=target(),doc=Object.assign(target(),{hidden,hasFocus:()=>focused});
 let time=1000,callback=null,frames=0,pauses=0;const resumes=[],loops=[];
 const gate=bindRenderActivity({doc,win,now:()=>time,setLoop:f=>{callback=f;loops.push(f);},frame:()=>frames++,onPause:()=>pauses++,onResume:gap=>resumes.push(gap)});
 return {gate,doc,win,resumes,loops,get frames(){return frames;},get callback(){return callback;},get pauses(){return pauses;},focus(value){focused=value;win.emit(value?'focus':'blur');},advance(ms){time+=ms;},frame(){callback?.(time);}};
}
test('visible but unfocused windows stop the actual loop, including queued frames',()=>{
 const t=harness();t.gate.setEnabled(true);t.frame();assert.equal(t.frames,1);
 const queued=t.callback;t.focus(false);assert.equal(t.callback,null);assert(!t.gate.running);
 t.advance(60000);for(let i=0;i<600;i++)queued(i);assert.equal(t.frames,1);
 t.focus(true);assert(t.gate.running);assert.deepEqual(t.resumes,[0,60000]);t.frame();assert.equal(t.frames,2);
 t.focus(true);assert.equal(t.resumes.length,2);assert.equal(t.pauses,1);
});
test('hidden tabs cannot restart on a focus event; visibility restores only focused tabs',()=>{
 const t=harness();t.gate.setEnabled(true);t.doc.hidden=true;t.doc.emit('visibilitychange');
 t.focus(true);assert(!t.gate.running);t.focus(false);t.doc.hidden=false;t.doc.emit('visibilitychange');assert(!t.gate.running);
 t.focus(true);assert(t.gate.running);
});
test('background startup and pre-entry pages do not start a loop',()=>{
 const t=harness({focused:false});t.gate.setEnabled(true);assert.equal(t.loops.length,0);
 t.focus(true);assert(t.gate.running);
 const waiting=harness();waiting.focus(true);waiting.doc.emit('visibilitychange');assert.equal(waiting.loops.length,0);
});
test('page cache restore obeys focus and a failed/disabled renderer stays stopped',()=>{
 const t=harness();t.gate.setEnabled(true);t.win.emit('pagehide');assert(!t.gate.running);
 t.focus(true);assert(!t.gate.running);t.win.emit('pageshow');assert(t.gate.running);
 t.gate.setEnabled(false);t.win.emit('pagehide');t.win.emit('pageshow');t.focus(true);assert(!t.gate.running);
});
test('disposing removes activity listeners and never restarts',()=>{
 const t=harness();t.gate.setEnabled(true);t.gate.dispose();const calls=t.loops.length;
 t.focus(false);t.focus(true);t.doc.emit('visibilitychange');t.gate.setEnabled(true);
 assert.equal(t.loops.length,calls);assert(!t.gate.running);
});
test('a missed focus event cancels even the RAF scheduled after the current callback',async()=>{
 const t=harness();t.gate.setEnabled(true);t.doc.hasFocus=()=>false;
 t.frame();assert(!t.gate.running);assert.equal(t.frames,0);
 const calls=t.loops.length;await Promise.resolve();
 assert.equal(t.loops.length,calls+1);assert.equal(t.callback,null);
});
