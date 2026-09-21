import test from 'node:test';
import assert from 'node:assert/strict';
import {createRecordsApi} from '../records-api.mjs';
const t=zh=>zh;
test('HTTP transport sends JSON, preserves teacher authorization and service errors',async()=>{
 const calls=[];const api=createRecordsApi({config:{url:'https://records.example'},t,fetchImpl:async(url,options)=>{calls.push({url,options});return new Response(JSON.stringify(url.endsWith('/bad')?{error:'教师口令不正确。'}:{ready:true}),{status:url.endsWith('/bad')?401:200});}});
 assert.deepEqual(await api('/api/health'),{ready:true});await api('/api/admin/records',{token:'test-token'});
 assert.equal(calls[1].options.headers.Authorization,'Bearer test-token');assert.equal(calls[1].options.credentials,'omit');
 await assert.rejects(()=>api('/bad',{method:'POST',body:{password:'test'}}),e=>e.status===401&&e.message==='教师口令不正确。');assert.equal(calls[2].options.body,'{"password":"test"}');
});
test('network failure has a useful message and a later retry works',async()=>{
 let calls=0;const api=createRecordsApi({config:{url:'https://records.example'},t,fetchImpl:async()=>{if(++calls===1)throw TypeError('Failed to fetch');return new Response('{"total":0}');}});
 await assert.rejects(()=>api('/api/records'),e=>e.message.includes('检查网络')&&!e.message.includes('Failed to fetch'));
 assert.deepEqual(await api('/api/records'),{total:0});
});
test('superseded requests can be cancelled without waiting for a response',async()=>{
 const controller=new AbortController();controller.abort();
 const api=createRecordsApi({config:{url:'https://records.example'},t,fetchImpl:async()=>new Promise(()=>{})});
 await assert.rejects(()=>api('/api/lookup',{signal:controller.signal}),e=>e.name==='AbortError');
});
