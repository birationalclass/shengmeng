import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {FrameQuality} from './frame-quality.js';
import {RenderBudget} from './render-budget.js';
import {readingPixelRatio} from './graphics-settings.js';
test('crisp priority keeps readable pixels at every fallback tier before and during entry',()=>{
 const quality=new FrameQuality(),gpu=new RenderBudget();
 for(let level=0;level<=5;level++){
  quality.level=level;
  const settings=quality.settings({reading:true,clarity:'crisp'});
  for(let now=0;now<30000;now+=250){gpu.sample(40,now);gpu.update(now,{reading:true,protectText:true});}
  assert.equal(Math.min(settings.scale,gpu.scale),1);
  assert(readingPixelRatio(.75,{enabled:true,width:1920,height:1080,dpr:1})>=1);
  if(level>=2){assert.equal(settings.cloud,'off');assert.equal(settings.shadow,0);}
 }
});
test('deferred assets wait for completion, recover from a failure and report final progress',async()=>{
 const source=(await readFile(new URL('./deferred-textures.js',import.meta.url),'utf8')).replace("import * as THREE from 'three';",'const THREE={};');
 const queue=await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
 const events=[],progress=[];
 queue.deferAsset(async()=>{await new Promise(r=>setTimeout(r,10));events.push('first');});
 queue.deferAsset(async()=>{events.push('failed');throw new Error('offline');});
 queue.deferAsset(async()=>{events.push('last');});
 assert.deepEqual(events,[]);
 await queue.startDeferredTextures(p=>progress.push(p));
 assert.deepEqual(events,['failed','last','first']);assert.equal(progress.at(-1),1);
 assert(progress.every((p,i)=>!i||p>=progress[i-1]));
});
