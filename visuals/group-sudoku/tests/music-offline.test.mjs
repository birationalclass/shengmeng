import test from 'node:test';
import assert from 'node:assert/strict';
import {byteRange,CHUNK_SIZE,chunkStream,offlineResponse} from '../music-cache.mjs';
import {downloadTrack} from '../music-offline.mjs';

test('media byte ranges support suffixes, open ends, clipping and invalid requests',()=>{
 assert.deepEqual(byteRange('bytes=3-6',10),{start:3,end:6,partial:true});
 assert.deepEqual(byteRange('bytes=-4',10),{start:6,end:9,partial:true});
 assert.deepEqual(byteRange('bytes=7-',10),{start:7,end:9,partial:true});
 assert.deepEqual(byteRange('bytes=7-90',10),{start:7,end:9,partial:true});
 for(const value of ['bytes=10-','bytes=7-2','bytes=-0','bytes=-','garbage'])assert.equal(byteRange(value,10),null);
 assert.deepEqual(byteRange(null,10),{start:0,end:9,partial:false});
});
test('offline response streams across chunks with exact 206, HEAD and 416 semantics',async()=>{
 const calls=[],get=async i=>{calls.push(i);return new Blob([new Uint8Array(i===0?CHUNK_SIZE:5).fill(i+1)]);};
 const req=new Request('https://test/audio',{headers:{Range:`bytes=${CHUNK_SIZE-2}-${CHUNK_SIZE+2}`}});
 const response=offlineResponse(req,{total:CHUNK_SIZE+5},get);
 assert.equal(calls.length,0);assert.equal(response.status,206);assert.equal(response.headers.get('Content-Length'),'5');
 assert.deepEqual([...new Uint8Array(await response.arrayBuffer())],[1,1,2,2,2]);assert.deepEqual(calls,[0,1]);
 const head=offlineResponse(new Request(req,{method:'HEAD'}),{total:CHUNK_SIZE+5},get);assert.equal(head.body,null);assert.equal(head.status,206);
 assert.equal(offlineResponse(new Request('https://test/audio',{headers:{Range:'bytes=50-'}}),{total:10},get).status,416);
 const reader=chunkStream(0,CHUNK_SIZE+4,get).getReader();await reader.read();const count=calls.length;await reader.cancel();await Promise.resolve();assert.equal(calls.length,count);
 await assert.rejects(()=>new Response(chunkStream(0,2,async()=>undefined)).arrayBuffer(),/missing/);
});
function fixture(){
 let meta;const blobs=new Map(),requests=[];
 const store={readMeta:async()=>meta,saveChunk:async(i,blob,value)=>{blobs.set(i,blob);meta={...value};},clearTrack:async()=>{blobs.clear();meta=undefined;}};
 const total=CHUNK_SIZE+11;
 const fetcher=async(url,{headers})=>{requests.push(headers);const start=Number(/bytes=(\d+)/.exec(headers.Range)[1]),end=Math.min(start+CHUNK_SIZE,total)-1;return new Response(new Uint8Array(end-start+1).fill(start?2:1),{status:206,headers:{'Content-Range':`bytes ${start}-${end}/${total}`,ETag:'"stable"'}});};
 return {store,fetcher,requests,blobs,total};
}
test('download persists bounded chunks, pauses and resumes without redownloading saved bytes',async()=>{
 const f=fixture(),controller=new AbortController();
 await assert.rejects(()=>downloadTrack({...f,signal:controller.signal,onProgress:()=>controller.abort()}),{name:'AbortError'});
 assert.equal((await f.store.readMeta()).bytes,CHUNK_SIZE);assert.equal(f.blobs.size,1);
 await downloadTrack({...f,signal:new AbortController().signal,onProgress:()=>{}});
 assert.equal(f.requests[1].Range,`bytes=${CHUNK_SIZE}-${2*CHUNK_SIZE-1}`);assert.equal(f.requests[1]['If-Range'],'"stable"');
 assert.equal((await f.store.readMeta()).complete,true);assert.equal(f.blobs.get(1).size,11);
});
test('rejects unbounded full responses, changed sources, truncated or oversized chunks',async()=>{
 const f=fixture(),base={...f,signal:new AbortController().signal,onProgress:()=>{}};let cancelled=false;
 await assert.rejects(()=>downloadTrack({...base,fetcher:async()=>new Response(new ReadableStream({cancel(){cancelled=true;}}))}),/range/);assert(cancelled);assert.equal(f.blobs.size,0);
 await f.store.saveChunk(0,new Blob(['x']),{bytes:CHUNK_SIZE,total:f.total,validator:'"old"',complete:false});
 await assert.rejects(()=>downloadTrack(base),/changed/);assert.equal(await f.store.readMeta(),undefined);
 for(const length of [10,CHUNK_SIZE+1])await assert.rejects(()=>downloadTrack({...base,fetcher:async()=>new Response(new Uint8Array(length),{status:206,headers:{'Content-Range':`bytes 0-${CHUNK_SIZE-1}/${f.total}`}})}),/range|truncated/);
});
