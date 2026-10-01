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

test('replaying completed stages sends no request while advances and failures still sync',async()=>{
 const data=new Map(),calls=[],journey={C4:{passed:1},S4:{passed:1}},account={id:'player'};
 const sync=createGeneratorSync({getAccount:()=>account,getJourney:()=>journey,read:k=>structuredClone(data.get(k)),write:(k,v)=>data.set(k,structuredClone(v)),onProgress:()=>{},api:async(path,options)=>{calls.push({path,options});return {journey:{}};}});
 sync.setSession({account,sessionToken:'token'});await new Promise(r=>setTimeout(r,10));calls.length=0;
 assert.equal(sync.enqueue({key:'C4',stage:0,won:true}),false);
 assert.equal(sync.enqueue({key:'S4',stage:0,won:true}),false);
 await new Promise(r=>setTimeout(r,10));assert.equal(calls.length,0);assert.equal(data.size,0);
 assert.equal(sync.enqueue({key:'S4',stage:1,won:true}),true);
 await new Promise(r=>setTimeout(r,10));assert.equal(calls.filter(c=>c.path.endsWith('/attempts')).length,1);
 calls.length=0;assert.equal(sync.enqueue({key:'C4',stage:0,won:false}),false);
 assert.equal(sync.enqueue({key:'S4',stage:0,won:false}),false);
 assert.equal(calls.length,0);assert.equal(sync.enqueue({key:'S5',stage:0,won:false}),true);
 await new Promise(r=>setTimeout(r,10));assert.equal(calls.filter(c=>c.path.endsWith('/attempts')).length,1);
});
test('offline first wins remain queued after local progress advances',async()=>{
 const data=new Map(),calls=[],journey={},account={id:'player'};
 const sync=createGeneratorSync({getAccount:()=>account,getJourney:()=>journey,read:k=>structuredClone(data.get(k)),write:(k,v)=>data.set(k,structuredClone(v)),onProgress:()=>{},api:async(path,options)=>{calls.push({path,options});return {journey:{}};}});
 assert.equal(sync.enqueue({key:'C4',stage:0,won:true}),true);journey.C4={passed:1};
 assert.equal(sync.enqueue({key:'C4',stage:0,won:true}),false);
 sync.setSession({account,sessionToken:'token'});await new Promise(r=>setTimeout(r,10));
 assert.equal(calls.filter(c=>c.path.endsWith('/attempts')).length,1);
});

test('an uncleared stage remains new even with a higher galaxy in local progress',async()=>{
 const {shouldSubmitAttempt}=await import('./generator-sync.mjs');
 const journey={S4:{passed:1},S5:{passed:1}};
 assert.equal(shouldSubmitAttempt({key:'S4',stage:1,won:false},journey),true);
 assert.equal(shouldSubmitAttempt({key:'S4',stage:0,won:false},journey),false);
});

test('record refresh awaits an ongoing upload and progress fetch',async()=>{
 const storage=new Map(),account={id:'guest'},calls=[];let release;
 const gate=new Promise(r=>{release=r;});
 const sync=createGeneratorSync({getAccount:()=>account,read:k=>storage.get(k),write:(k,v)=>storage.set(k,v),onProgress:()=>{},api:async(path)=>{calls.push(path);if(path.endsWith('/attempts'))await gate;return {journey:{}};}});
 sync.enqueue({key:'C4',stage:0});sync.setSession({account,sessionToken:'token'});
 await new Promise(r=>setTimeout(r,0));let refreshed=false;const waiting=sync.flush().then(()=>{refreshed=true;});
 await new Promise(r=>setTimeout(r,0));assert.equal(refreshed,false);release();await waiting;
 assert.equal(calls.filter(p=>p.endsWith('/attempts')).length,1);assert.ok(calls.some(p=>p.endsWith('/progress')));
});
