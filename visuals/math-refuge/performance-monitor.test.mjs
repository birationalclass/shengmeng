import test from 'node:test';
import assert from 'node:assert/strict';
import {summarizeFrames,createPerformanceMonitor} from './performance-monitor.js';
test('FPS uses elapsed frame time and includes long stalls',()=>{
 const steady=Array.from({length:60},()=>({ms:1000/60,cpu:3}));
 assert(Math.abs(summarizeFrames(steady).fps-60)<.001);
 assert(Math.abs(summarizeFrames([...steady,{ms:1000,cpu:25}]).fps-30.5)<.001);
 assert.equal(summarizeFrames([{ms:16,cpu:2},{ms:100,cpu:40}]).p95,100);
 assert.equal(summarizeFrames([]),null);
});
test('panel is idle while closed, throttles DOM work and labels unsupported GPU',()=>{
 const elements=new Map(),events={};let writes=0;
 const doc={hidden:false,addEventListener:(k,f)=>events[k]=f,getElementById:id=>{
  if(!elements.has(id))elements.set(id,{hidden:id==='performancePanel',attributes:{},events:{},addEventListener(k,f){this.events[k]=f;},setAttribute(k,v){this.attributes[k]=v;writes++;},focus(){},set textContent(v){this.text=v;writes++;}});
  return elements.get(id);
 }};
 const monitor=createPerformanceMonitor(doc),renderer={domElement:{width:780,height:1688},info:{render:{calls:120,triangles:2000},memory:{textures:8,geometries:30}}};
 monitor.frame(1000,16,3,renderer);assert.equal(writes,0);
 elements.get('performanceButton').events.click();assert(monitor.visible);
 monitor.frame(1100,16,3,renderer);assert.equal(elements.get('performanceGPU').text,'浏览器不支持');
 const first=writes;monitor.frame(1200,16,3,renderer);assert.equal(writes,first);
 monitor.gpu(7,1500);monitor.frame(1700,16,3,renderer,{gpuSupported:true});assert.equal(elements.get('performanceGPU').text,'7.0 ms');
 monitor.setPaused(true);assert.equal(elements.get('performanceFPS').text,'—');assert.match(elements.get('performanceStatus').text,/渲染已暂停/);
 const pausedWrites=writes;monitor.frame(2300,16,3,renderer);assert.equal(writes,pausedWrites);
 monitor.setPaused(false);monitor.frame(2500,16,3,renderer);assert.equal(elements.get('performanceFPS').text,'63');
 doc.hidden=true;events.visibilitychange();assert.equal(elements.get('performanceFPS').text,'—');
 events.keydown({key:'Escape'});assert(!monitor.visible);
});
