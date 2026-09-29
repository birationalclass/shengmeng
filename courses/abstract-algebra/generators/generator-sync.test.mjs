import test from 'node:test';
import assert from 'node:assert/strict';
import {createGeneratorSync} from './generator-sync.mjs';
test('outbox retries with stable IDs and never submits another account records',async()=>{
 const data=new Map(),sent=[];let account={id:'one'},fail=true;
 const sync=createGeneratorSync({getAccount:()=>account,read:k=>structuredClone(data.get(k)),write:(k,v)=>data.set(k,structuredClone(v)),onProgress:()=>{},api:async(path,options)=>{if(path.endsWith('/attempts')){sent.push(options);if(fail)throw Object.assign(Error('offline'),{status:400});}return {journey:{}};}});
 sync.enqueue({key:'C4',stage:0,seeds:[1],seconds:2});
 sync.setSession({account,sessionToken:'one-token'});await new Promise(r=>setTimeout(r,20));
 assert.equal(data.get('generators-outbox-v1:one').length,1);
 account={id:'two'};await sync.flush();assert.equal(sent.length,1);
 account={id:'one'};fail=false;await sync.flush();
 assert.equal(sent[0].body.submissionId,sent[1].body.submissionId);assert.equal(data.get('generators-outbox-v1:one').length,0);
});
