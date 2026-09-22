import test from 'node:test';
import assert from 'node:assert/strict';
import {createConnection,reconnectDelay} from '../connection.mjs';
function setup(run){let online=true,visible=true,seq=0;const timers=new Map(),states=[];const connection=createConnection({run,onState:s=>states.push(s),online:()=>online,visible:()=>visible,random:()=>1,setTimer:(fn,ms)=>{timers.set(++seq,{fn,ms});return seq;},clearTimer:id=>timers.delete(id)});return {connection,timers,states,setOnline:v=>online=v,setVisible:v=>visible=v,async tick(){const [id,job]=timers.entries().next().value;timers.delete(id);await job.fn();}};}
test('backoff is bounded and jittered; reconnection resets to healthy heartbeat',async()=>{
 assert.deepEqual([1,2,3,4,5,6,99].map(n=>reconnectDelay(n,()=>1)),[2000,4000,8000,16000,32000,60000,60000]);assert.equal(reconnectDelay(99,()=>0),48000);
 let failed=true,calls=0;const f=setup(async()=>{calls++;if(failed)throw Error('offline');});
 await f.tick();assert.equal([...f.timers.values()][0].ms,2000);await f.tick();assert.equal([...f.timers.values()][0].ms,4000);
 failed=false;f.connection.wake();await f.tick();assert.equal(f.connection.state,'connected');assert.equal([...f.timers.values()][0].ms,60000);assert.equal(calls,3);
});
test('only one request chain runs; offline and background stop traffic; return reconnects immediately',async()=>{
 let resolve,calls=0;const f=setup(({signal})=>{calls++;return new Promise(r=>{resolve=r;signal.addEventListener('abort',()=>r());});});
 const running=f.tick();f.connection.wake();f.connection.wake();assert.equal(calls,1);resolve();await running;assert.equal(f.timers.size,1);
 f.setOnline(false);f.connection.wake();assert.equal(f.connection.state,'offline');assert.equal(f.timers.size,0);
 f.setOnline(true);f.connection.wake();const resumed=f.tick();assert.equal(calls,2);f.setVisible(false);f.connection.wake();await resumed;assert.equal(f.timers.size,0);
 f.setVisible(true);f.connection.wake();const foreground=f.tick();resolve();await foreground;assert.equal(f.connection.state,'connected');
 f.connection.pause();assert.equal(f.timers.size,0);f.connection.wake();assert.equal(f.timers.size,1);f.connection.stop();assert.equal(f.timers.size,0);
});
