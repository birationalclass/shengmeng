import test from 'node:test';import assert from 'node:assert/strict';import {createResourceFetch} from './resource-fetch.js';import {AssetRetry} from './asset-retry.js';import {ResourceScheduler} from './resource-scheduler.js';import {createCoursePreload} from './course-preload.js';import {createReportVoice} from './report-voice.js';
import vm from 'node:vm';import {readFileSync} from 'node:fs';
test('stalled response headers abort the actual request while unrelated work keeps running',async()=>{
 let signal,ticks=0;const timer=setInterval(()=>ticks++,2),fetcher=createResourceFetch((_,o)=>{signal=o.signal;return new Promise(()=>{});},{idleTimeout:25});
 try{await assert.rejects(fetcher('https://test/stuck'),e=>e.name==='TimeoutError');assert(signal.aborted);assert(ticks>1);}finally{clearInterval(timer);}
});
test('a response that stalls after its first bytes cancels the body and releases the reader',async()=>{
 let canceled=false;const fetcher=createResourceFetch(async()=>new Response(new ReadableStream({start(c){c.enqueue(new Uint8Array([1,2,3]));},cancel(){canceled=true;}})),{idleTimeout:25});
 const response=await fetcher('https://test/body');await assert.rejects(response.arrayBuffer(),e=>e.name==='TimeoutError');assert(canceled);
});
test('healthy chunked downloads survive longer than the idle limit when bytes keep arriving',async()=>{
 let timer;const fetcher=createResourceFetch(async()=>new Response(new ReadableStream({start(c){let n=0;timer=setInterval(()=>{c.enqueue(new Uint8Array([n++]));if(n===8){clearInterval(timer);c.close();}},5);},cancel(){clearInterval(timer);}})),{idleTimeout:25});
 assert.equal((await(await fetcher('https://test/slow')).arrayBuffer()).byteLength,8);
});
test('canceling an in-flight request releases even a fetcher that ignores abort',async()=>{
 const controller=new AbortController(),fetcher=createResourceFetch(()=>new Promise(()=>{}),{idleTimeout:1000}),job=fetcher('https://test/cancel',{signal:controller.signal});controller.abort();await assert.rejects(job,e=>e.name==='AbortError');
});
test('two stalled background downloads leave capacity for the current board and queued cancellation',async()=>{
 const controllers=[new AbortController(),new AbortController(),new AbortController()];let started=[];
 const fetcher=createResourceFetch(async src=>{started.push(src);return src.includes('background')?new Promise(()=>{}):new Response('current board');},{idleTimeout:1000});
 const jobs=controllers.map((c,i)=>fetcher('https://test/background'+i,{priority:'low',signal:c.signal}));const outcomes=Promise.allSettled(jobs);
 assert.equal(started.length,2);assert.equal(await(await fetcher('https://test/current')).text(),'current board');controllers.forEach(c=>c.abort());await outcomes;assert.equal(started.length,3,'canceled queued background never starts');
});
test('repeated rendered frames cannot hammer a failed asset; explicit retry clears its backoff',async()=>{
 let now=0,calls=0;const retry=new AssetRetry({now:()=>now});retry.fail(5,Error('offline'));
 for(let frame=0;frame<1800;frame++)if(!retry.blocked(5))calls++;
 assert.equal(calls,0);assert(retry.blocked(5));now=2001;assert.equal(retry.blocked(5),null);retry.fail(5,Error('offline'));now=4002;assert(retry.blocked(5),'second failure backs off longer');retry.clear(5);assert.equal(retry.blocked(5),null);
});
test('the actual board loader retains failed request backoff after clearing its pending entry',async()=>{
 const source=readFileSync(new URL('./lecture.js',import.meta.url),'utf8'),method=source.slice(source.indexOf('  function load('),source.indexOf('  if(!disabled&&hasSelection)'));
 let calls=0;const c={cache:new Map(),pending:new Map(),assetRetry:new AssetRetry({now:()=>0}),generation:0,language:'en',writingStyle:'refined',Image:class{},canAuthor:true,pages:[{formulaAsset:'broken.svg'}],authoredFormula:()=>{calls++;return Promise.reject(Error('offline'));},withDeadline:p=>p};
 const load=vm.runInNewContext(method+';load',c);await assert.rejects(load(0),/offline/);assert.equal(c.pending.size,0);
 for(let i=0;i<300;i++)await assert.rejects(load(0),/offline/);assert.equal(calls,1);c.assetRetry.clear(0);await assert.rejects(load(0),/offline/);assert.equal(calls,2);
});
test('a hung optional job releases the scheduler, and retrying its key can succeed',async()=>{
 const s=new ResourceScheduler({taskTimeout:25,api:{setTimeout,performance,requestIdleCallback:cb=>setTimeout(cb,0)}});let signal,ran=false;
 const broken=s.enqueue('bad','故障资源',s=>{signal=s;return new Promise(()=>{});});const checked=assert.rejects(broken,/超时/),next=s.enqueue('good','其他资源',()=>ran=true);
 await checked;await next;assert(signal.aborted);assert(ran);assert.equal(s.snapshot().active,false);await s.enqueue('bad','故障资源',()=>true);
});
test('a stalled course prefetch ends locally instead of occupying both workers forever',async()=>{
 const q=createCoursePreload({fetcher:()=>new Promise(()=>{}),requestTimeout:25,baseURL:'https://test/'});await q.start([{formulaAsset:'a.svg'},{formulaAsset:'b.svg'},{formulaAsset:'c.svg'}]);assert.equal(q.state.phase,'partial');assert.equal(q.state.completed,0);assert.equal(q.state.retrying,q.state.total);assert(q.state.errors.length>0);q.cancel();
});
test('a parked optional task cannot deadlock required startup resources behind the opening gate',async()=>{
 let opening=true;const s=new ResourceScheduler({policy:()=>({opening}),api:{setTimeout,performance,requestIdleCallback:cb=>setTimeout(cb,0)}});let optional=false;
 const parked=s.enqueue('optional','环境细节',()=>optional=true);await s.enqueue('required','首屏必需',()=>{}, {priority:0});assert(!optional);opening=false;await parked;assert(optional);
});
class Audio extends EventTarget{currentTime=0;pause(){}async play(){this.dispatchEvent(new Event('playing'));}}
test('an audio stall becomes a retryable error and recovers without reloading the page',async()=>{
 let offline=true;const v=createReportVoice({requestTimeout:25,baseURL:'https://test/',fetcher:async src=>src.endsWith('.json')?Response.json({duration:10,boards:[{page:0,start:0,end:10}],chapters:[{src:'a.mp3',start:0,duration:10}]}):offline?new Promise(()=>{}):new Response('audio'),makeAudio:()=>new Audio(),makeURL:()=> 'blob:test',revokeURL(){}});
 assert.equal(await v.select({id:'test',narration:{manifest:'n.json'}},{autoplay:true}),false);assert.equal(v.state.phase,'error');offline=false;await v.toggle();assert.equal(v.state.phase,'playing');v.dispose();
});
