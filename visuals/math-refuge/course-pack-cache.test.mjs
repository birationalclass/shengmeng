import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {gzipSync} from 'node:zlib';
import {createCoursePackStore} from './course-pack-cache.js';
const root='https://test.invalid/visuals/math-refuge/';
const sha=data=>createHash('sha256').update(data).digest('hex');
function fixture({storage=true,delay=false}={}){
 const bytes=gzipSync(JSON.stringify({version:2,assets:{'assets/a.svg':{type:'image/svg+xml',body:Buffer.from('<svg>A</svg>').toString('base64')},'assets/voice.mp3':{type:'audio/mpeg',body:Buffer.from([0,255,2,3]).toString('base64')}}}));
 const pack={url:'./assets/course-packs/v1/sample-'+sha(bytes).slice(0,20)+'.json.gz',sha256:sha(bytes),bytes:bytes.length,expandedBytes:999,files:['assets/a.svg','assets/voice.mp3']};
 const index=Buffer.from(JSON.stringify({version:1,id:'test',base:'../../../',packs:[pack]}));const program={resourceIndex:'./assets/course-packs/v1/test-'+sha(index).slice(0,20)+'.json'};
 const disk=new Map(),calls=[];let release,aborts=0;
 const cache={async match(u){const b=disk.get(u);return b?new Response(b):undefined;},async put(u,r){disk.set(u,new Uint8Array(await r.arrayBuffer()));},async delete(u){return disk.delete(u);}};
 const backing=storage?{open:async()=>cache}:{open:async()=>{throw Error('cache unavailable');}};
 const fetcher=async(u,o={})=>{u=String(u);calls.push(u);if(u.endsWith('.json.gz')){if(delay)await new Promise((resolve,reject)=>{release=resolve;o.signal.addEventListener('abort',()=>{aborts++;reject(o.signal.reason);},{once:true});});return new Response(bytes);}if(u.endsWith('.json'))return new Response(index);return new Response('original');};fetcher.promote=()=>true;
 const store=()=>createCoursePackStore({baseURL:root,storage:backing});
 return {bytes,pack,program,disk,calls,fetcher,store,release:()=>release?.(),get aborts(){return aborts;}};
}
test('exact original bytes, MIME type, and one fetch for concurrent files',async()=>{
 const f=fixture(),s=f.store();await s.register(f.program,{fetcher:f.fetcher});const [a,b]=await Promise.all([s.response(root+'assets/a.svg?v=old',{},f.fetcher),s.response(root+'assets/voice.mp3',{},f.fetcher)]);
 assert.equal(await a.text(),'<svg>A</svg>');assert.equal(a.headers.get('content-type'),'image/svg+xml');assert.deepEqual([...new Uint8Array(await b.arrayBuffer())],[0,255,2,3]);assert.equal(f.calls.filter(x=>x.endsWith('.gz')).length,1);
});
test('a new page instance reads index and compressed pack from persistent cache without network',async()=>{
 const f=fixture(),s=f.store();await s.register(f.program,{fetcher:f.fetcher});await(await s.response(root+'assets/a.svg',{},f.fetcher)).text();
 const second=f.store(),offline=()=>{throw Error('network disabled');};await second.register(f.program,{fetcher:offline});assert.equal(await(await second.response(root+'assets/a.svg',{},offline)).text(),'<svg>A</svg>');assert.equal(second.state.diskHits,2);
});
test('corrupt cached pack is evicted and fetched again',async()=>{
 const f=fixture(),s=f.store();await s.register(f.program,{fetcher:f.fetcher});f.disk.set(new URL(f.pack.url,root).href,new Uint8Array([1,2,3]));assert.equal(await(await s.response(root+'assets/a.svg',{},f.fetcher)).text(),'<svg>A</svg>');assert.equal(s.state.corruptEntries,1);
});
test('cache denied still loads and reuses the in-memory pack',async()=>{
 const f=fixture({storage:false}),s=f.store();await s.register(f.program,{fetcher:f.fetcher});await s.response(root+'assets/a.svg',{},f.fetcher);await s.response(root+'assets/voice.mp3',{},f.fetcher);assert.equal(s.state.memoryHits,1);assert.equal(s.state.originalFallbacks,0);
});
test('cancel one waiter without cancelling another active file in the same pack',async()=>{
 const f=fixture({delay:true}),s=f.store();await s.register(f.program,{fetcher:f.fetcher});const c=new AbortController(),first=s.response(root+'assets/a.svg',{signal:c.signal},f.fetcher),second=s.response(root+'assets/voice.mp3',{},f.fetcher);c.abort();await assert.rejects(first);await new Promise(r=>setTimeout(r,10));f.release();assert.equal((await second).status,200);assert.equal(f.aborts,0);
});
test('cancelling the final waiter aborts the transfer and permits retry',async()=>{
 const f=fixture({delay:true}),s=f.store();await s.register(f.program,{fetcher:f.fetcher});const c=new AbortController(),first=s.response(root+'assets/a.svg',{signal:c.signal},f.fetcher);await new Promise(r=>setTimeout(r,10));c.abort();await assert.rejects(first);assert.equal(f.aborts,1);await new Promise(r=>setTimeout(r,10));const retry=s.response(root+'assets/a.svg',{},f.fetcher);await new Promise(r=>setTimeout(r,10));f.release();assert.equal(await(await retry).text(),'<svg>A</svg>');
});
test('failed pack falls back to original URL; unsupported decompression skips pack mode',async()=>{
 const f=fixture(),s=f.store();await s.register(f.program,{fetcher:f.fetcher});const fail=(u)=>String(u).endsWith('.gz')?Promise.resolve(new Response('',{status:503})):f.fetcher(u);assert.equal(await(await s.response(root+'assets/a.svg',{},fail)).text(),'original');assert.equal(s.state.originalFallbacks,1);const old=createCoursePackStore({baseURL:root,enabled:()=>false});assert.equal(await old.register(f.program,{fetcher:f.fetcher}),false);assert.equal(old.response(root+'assets/a.svg'),null);
});
