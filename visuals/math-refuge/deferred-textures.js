import {fetchProgressBlob} from './resource-progress.js';
import * as THREE from 'three';
let executor=null,upload=null;export function setDeferredExecutor(value,publish){executor=value;upload=publish;}
async function run(job){const result=job();if(result?.next){for(;;){const step=await result.next();if(step.done)return;await (typeof step.value==='function'?step.value():step.value);}}else await result;}
const pending=[],startedPhases=new Set(),phaseCounts=new Map();let criticalStarted=false,allStarted=false,running=0,limit=3,completed=0,total=0,criticalCompleted=0,criticalTotal=0;const observers=new Set();
function notify(){
 for(const item of [...observers]){
  const phase=item.phase&&phaseCounts.get(item.phase),done=item.phase?(phase?.done||0):item.criticalOnly?criticalCompleted:completed,count=item.phase?(phase?.total||0):item.criticalOnly?criticalTotal:total;
  item.report(count?done/count:1);
  if(done===count){observers.delete(item);item.resolve();}
 }
}
function pump(){
 while(running<limit){
  const available=item=>allStarted||(criticalStarted&&item.critical)||startedPhases.has(item.phase);
  let index=pending.findIndex(item=>available(item)&&item.phase==='entry');
  if(index<0)index=pending.findIndex(item=>available(item)&&item.critical);
  if(index<0)index=pending.findIndex(available);if(index<0)break;
  const item=pending.splice(index,1)[0];running++;
  Promise.resolve().then(()=>executor?executor(item):item.prepare?Promise.resolve(item.prepare()).then(()=>run(item.job)):run(item.job)).catch(()=>{}).finally(()=>{running--;completed++;phaseCounts.get(item.phase).done++;if(item.critical)criticalCompleted++;notify();setTimeout(pump,0);});
 }
 notify();
}
export function startDeferredTextures(report=()=>{},{criticalOnly=false,concurrency=3,phase=null}={}){
 if(phase)startedPhases.add(phase);else{criticalStarted=true;if(!criticalOnly)allStarted=true;}limit=Math.max(1,Math.min(3,concurrency));
 return new Promise(resolve=>{observers.add({report,resolve,criticalOnly,phase});pump();});
}
export function deferAsset(job,{critical=false,phase=critical?'hall':'background',prepare=null}={}){total++;if(critical)criticalTotal++;if(!phaseCounts.has(phase))phaseCounts.set(phase,{done:0,total:0});phaseCounts.get(phase).total++;pending.push({job,prepare,critical,phase,id:total});pump();}
export function deferredTexture(url,{critical=false,phase=critical?'hall':'background'}={}){
 const canvas=document.createElement('canvas');canvas.width=canvas.height=1;
 const ctx=canvas.getContext('2d');ctx.fillStyle=/normal|waternormals/.test(url)?'rgb(128,128,255)':'white';ctx.fillRect(0,0,1,1);
 const map=new THREE.CanvasTexture(canvas);
 let image;
 const prepare=async()=>{try{const blob=await fetchProgressBlob(url);if(globalThis.createImageBitmap)image=await createImageBitmap(blob,{imageOrientation:'flipY',premultiplyAlpha:'none',colorSpaceConversion:'none'});else{const src=URL.createObjectURL(blob);try{const loaded=await new THREE.TextureLoader().loadAsync(src);image=loaded.image;loaded.dispose();}finally{URL.revokeObjectURL(src);}}}catch{}};
 // Required downloads may overlap; publication stays in one bounded render turn.
 deferAsset(function*(){yield ()=>{if(image){map.image=image;map.needsUpdate=true;upload?.(map);}};},{critical,phase,prepare});return map;
}
