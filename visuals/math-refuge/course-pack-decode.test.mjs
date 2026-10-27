import test from 'node:test';import assert from 'node:assert/strict';import{createHash}from'node:crypto';
import {decodeCourseBase64} from './course-pack-decode.js';
test('large compressed-course audio decodes byte-exactly and fallback yields between bounded slices',async()=>{
 const source=Buffer.alloc(4*1024*1024+31);for(let i=0;i<source.length;i++)source[i]=(i*71+19)%256;
 let turns=0;const bytes=await decodeCourseBase64(source.toString('base64'),{native:null,yieldTask:async()=>{turns++;}});
 assert.equal(createHash('sha256').update(bytes).digest('hex'),createHash('sha256').update(source).digest('hex'));assert.equal(turns,16);
});
test('native decoder preserves binary bytes and does not schedule unnecessary fallback work',async()=>{
 const source=Buffer.from([0,255,128,17,0,127]);let calls=0;const bytes=await decodeCourseBase64(source.toString('base64'),{native:value=>{calls++;return new Uint8Array(Buffer.from(value,'base64'));},yieldTask:()=>assert.fail('native decoder must not use fallback')});assert.deepEqual(bytes,new Uint8Array(source));assert.equal(calls,1);
});
test('cancelled audio readers stop before decoding or after their next bounded slice',async()=>{
 const first=new AbortController();first.abort();await assert.rejects(decodeCourseBase64('AA==',{signal:first.signal}),{name:'AbortError'});
 const second=new AbortController();let turns=0;await assert.rejects(decodeCourseBase64(Buffer.alloc(2*1024*1024).toString('base64'),{native:null,signal:second.signal,yieldTask:async()=>{turns++;second.abort();}}),{name:'AbortError'});assert.equal(turns,1);
});
