import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {OpeningPerformance} from './opening-performance.js';
import {ResourceScheduler} from './resource-scheduler.js';
import {loadBoardFonts} from './staged-startup.js';
test('all required board fonts start together before report content is available',async()=>{
 const started=[],finish=[];const job=loadBoardFonts({fonts:{load(font){started.push(font);return new Promise(r=>finish.push(r));}}});
 assert.equal(started.length,3);let done=false;job.then(()=>done=true);finish[0]();await Promise.resolve();assert.equal(done,false);finish.slice(1).forEach(r=>r());await job;assert.equal(done,true);
 await loadBoardFonts({});
});
test('whole-flight metrics retain rare stalls outside a rolling sample window',()=>{
 const m=new OpeningPerformance();m.start(1000);m.sample(180,4);for(let i=0;i<1000;i++)m.sample(16,3);
 const r=m.finish(17000);assert.equal(r.maxFrameMs,180);assert.equal(r.over100ms,1);assert.equal(r.frameP95,16);assert.equal(r.durationMs,16000);
 m.sample(300,40);assert.equal(m.snapshot().frames,1001);m.start(18000);assert.equal(m.snapshot().over100ms,0);
});
test('a slow preview cannot add background cooldowns to required hall work',async()=>{
 const delays=[],s=new ResourceScheduler({policy:()=>({entered:true,opening:true,targetFPS:60}),api:{performance,setTimeout(fn,ms){delays.push(ms);setTimeout(fn,0);}}});
 s.frame(90,30);await s.enqueue('hall','必需材质',function*(){yield ()=>{};yield ()=>{};},{priority:0});assert(delays.length>0);assert(delays.every(ms=>ms===0));
});
test('required downloads overlap but remain bounded to two requests',async()=>{
 const source=readFileSync(new URL('./deferred-textures.js',import.meta.url),'utf8').replace("import * as THREE from 'three';",'const THREE={};').replace("import {fetchProgressBlob} from './resource-progress.js';",'const fetchProgressBlob=()=>{};');
 const q=await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
 let running=0,peak=0,published=0;for(let i=0;i<6;i++)q.deferAsset(()=>published++,{phase:'hall',prepare:async()=>{running++;peak=Math.max(peak,running);await new Promise(r=>setTimeout(r,3));running--;}});
 await q.startDeferredTextures(()=>{},{phase:'hall',concurrency:2});assert.equal(peak,2);assert.equal(published,6);
});
test('built entry graph stays small and leaves hall and upper-floor code behind dynamic imports',()=>{
 const {outputs}=JSON.parse(readFileSync(new URL('./opening-bundles.json',import.meta.url),'utf8'));
 const seen=new Set(),inputs=new Set();function visit(path){if(seen.has(path))return;seen.add(path);const output=outputs.find(o=>o.path===path);assert(output,path);assert.equal(Buffer.byteLength(readFileSync(new URL(path,import.meta.url))),output.bytes);output.inputs.forEach(p=>inputs.add(p));for(const item of output.imports)if(item.kind==='import-statement')visit(item.path);}
 visit('refuge-app.js');visit('refuge-social.js');visit('refuge-meter.js');assert(seen.size<=10);assert(!inputs.has('lecture.js'));assert(!inputs.has('upper-lounge.js'));assert(inputs.has('scene.js'));
 for(const output of outputs)for(const item of output.imports)if(item.kind==='dynamic-import')assert(outputs.some(o=>o.path===item.path),item.path);
});
