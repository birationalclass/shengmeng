import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {waitForEntered,idleTurn,createOpeningPreparation} from './staged-startup.js';
test('resource readiness never authorizes interactive entry',async()=>{
 const target=new EventTarget(),node={dataset:{entered:'false',ready:'true'}};let ran=false;
 const task=waitForEntered(node,target).then(()=>ran=true);
 target.dispatchEvent(new Event('refuge-entry'));target.dispatchEvent(new Event('refuge-entered'));await Promise.resolve();assert.equal(ran,false);
 node.dataset.entered='true';target.dispatchEvent(new Event('refuge-entered'));await task;assert.equal(ran,true);
});
test('required room and GPU preparation finish without authentication or an entry click',async()=>{
 const node={dataset:{ready:'true',entered:'false'}},events=[];let finish;
 const prepare=createOpeningPreparation({node,prepareRoom:()=>{events.push('room');return new Promise(r=>finish=r);},prepareGPU:()=>events.push('gpu'),now:()=>12});
 const job=prepare();assert.equal(prepare(),job);await Promise.resolve();assert.deepEqual(events,['room']);assert.equal(node.dataset.openingPreparation,'loading');assert.equal(node.dataset.entered,'false');
 finish();await job;assert.deepEqual(events,['room','gpu']);assert.equal(node.dataset.openingPreparation,'ready');assert.equal(node.dataset.preparedBeforeEntry,'true');assert.equal(node.dataset.entered,'false');assert.equal(prepare(),job);
});
test('a click during preparation shares the job and cannot compile a second copy',async()=>{
 const node={dataset:{entered:'false'}},events=[];let finish;
 const prepare=createOpeningPreparation({node,prepareRoom:()=>new Promise(r=>finish=r),prepareGPU:()=>events.push('gpu')});const background=prepare();await Promise.resolve();node.dataset.entered='true';const entered=prepare();assert.equal(entered,background);finish();await entered;assert.deepEqual(events,['gpu']);assert.equal(node.dataset.preparedBeforeEntry,'false');
});
test('preparation failure is retryable without changing entry authorization',async()=>{
 const node={dataset:{entered:'false'}},error=new Error('offline');let calls=0;
 const prepare=createOpeningPreparation({node,prepareRoom:()=>{if(++calls===1)throw error;},prepareGPU:()=>{}});
 await assert.rejects(prepare(),error);assert.equal(node.dataset.openingPreparation,'error');assert.equal(node.dataset.entered,'false');await prepare();assert.equal(node.dataset.openingPreparation,'ready');assert.equal(node.dataset.preparationError,undefined);
});
test('a late subscriber to entry does not miss the already completed event',async()=>{
 await waitForEntered({dataset:{entered:'true'}},new EventTarget());
});
test('background jobs yield a turn with a bounded idle timeout',async()=>{
 let timeout;await idleTurn({requestIdleCallback(resolve,options){timeout=options.timeout;resolve();}});assert.equal(timeout,750);
 let delay;await idleTurn({setTimeout(resolve,ms){delay=ms;resolve();}});assert.equal(delay,32);
});
test('entry textures cannot accidentally start hall or background texture jobs',async()=>{
 const source=readFileSync(new URL('./deferred-textures.js',import.meta.url),'utf8').replace("import * as THREE from 'three';",'const THREE={};').replace("import {fetchProgressBlob} from './resource-progress.js';",'const fetchProgressBlob=()=>{};');
 const {deferAsset,startDeferredTextures}=await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));const loaded=[];
 deferAsset(()=>loaded.push('hall'),{critical:true,phase:'hall'});deferAsset(()=>loaded.push('background'),{phase:'background'});deferAsset(()=>loaded.push('entry'),{critical:true,phase:'entry'});
 await startDeferredTextures(()=>{},{phase:'entry',concurrency:1});assert.deepEqual(loaded,['entry']);
 await startDeferredTextures(()=>{},{phase:'hall',concurrency:1});assert.deepEqual(loaded,['entry','hall']);
 await startDeferredTextures(()=>{},{concurrency:1});assert.deepEqual(loaded,['entry','hall','background']);
});
