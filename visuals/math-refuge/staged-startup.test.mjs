import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {waitForEntered,idleTurn} from './staged-startup.js';
test('authentication and a prepared preview cannot start post-entry work before actual entry',async()=>{
 const target=new EventTarget(),node={dataset:{entered:'false',ready:'true'}};let ran=false;
 const task=waitForEntered(node,target).then(()=>ran=true);
 target.dispatchEvent(new Event('refuge-entry'));target.dispatchEvent(new Event('refuge-entered'));await Promise.resolve();assert.equal(ran,false);
 node.dataset.entered='true';target.dispatchEvent(new Event('refuge-entered'));await task;assert.equal(ran,true);
});
test('a late subscriber to entry does not miss the already completed event',async()=>{
 await waitForEntered({dataset:{entered:'true'}},new EventTarget());
});
test('background jobs yield a turn with a bounded idle timeout',async()=>{
 let timeout;await idleTurn({requestIdleCallback(resolve,options){timeout=options.timeout;resolve();}});assert.equal(timeout,750);
 let delay;await idleTurn({setTimeout(resolve,ms){delay=ms;resolve();}});assert.equal(delay,32);
});
test('entry textures cannot accidentally start hall or background texture jobs',async()=>{
 const source=readFileSync(new URL('./deferred-textures.js',import.meta.url),'utf8').replace("import * as THREE from 'three';",'const THREE={};');
 const {deferAsset,startDeferredTextures}=await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));const loaded=[];
 deferAsset(()=>loaded.push('hall'),{critical:true,phase:'hall'});deferAsset(()=>loaded.push('background'),{phase:'background'});deferAsset(()=>loaded.push('entry'),{critical:true,phase:'entry'});
 await startDeferredTextures(()=>{},{phase:'entry',concurrency:1});assert.deepEqual(loaded,['entry']);
 await startDeferredTextures(()=>{},{phase:'hall',concurrency:1});assert.deepEqual(loaded,['entry','hall']);
 await startDeferredTextures(()=>{},{concurrency:1});assert.deepEqual(loaded,['entry','hall','background']);
});
