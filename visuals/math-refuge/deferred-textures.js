import * as THREE from 'three';
const pending=[];let criticalStarted=false,allStarted=false,running=0,limit=3,completed=0,total=0,criticalCompleted=0,criticalTotal=0;const observers=new Set();
function notify(){
 for(const item of [...observers]){
  const done=item.criticalOnly?criticalCompleted:completed,count=item.criticalOnly?criticalTotal:total;
  item.report(count?done/count:1);
  if(done===count){observers.delete(item);item.resolve();}
 }
}
function pump(){
 while(running<limit){
  let index=criticalStarted?pending.findIndex(item=>item.critical):-1;
  if(index<0&&allStarted)index=pending.findIndex(item=>!item.critical);if(index<0)break;
  const item=pending.splice(index,1)[0];running++;
  Promise.resolve().then(item.job).catch(()=>{}).finally(()=>{running--;completed++;if(item.critical)criticalCompleted++;notify();setTimeout(pump,0);});
 }
 notify();
}
export function startDeferredTextures(report=()=>{},{criticalOnly=false,concurrency=3}={}){
 criticalStarted=true;if(!criticalOnly)allStarted=true;limit=Math.max(1,Math.min(3,concurrency));
 return new Promise(resolve=>{observers.add({report,resolve,criticalOnly});pump();});
}
export function deferAsset(job,{critical=false}={}){total++;if(critical)criticalTotal++;pending.push({job,critical});pump();}
export function deferredTexture(url,{critical=false}={}){
 const canvas=document.createElement('canvas');canvas.width=canvas.height=1;
 const ctx=canvas.getContext('2d');ctx.fillStyle=/normal|waternormals/.test(url)?'rgb(128,128,255)':'white';ctx.fillRect(0,0,1,1);
 const map=new THREE.CanvasTexture(canvas);
 deferAsset(async()=>{try{const loaded=await new THREE.TextureLoader().loadAsync(url);map.image=loaded.image;map.needsUpdate=true;loaded.dispose();}catch{/* Retain the neutral material if offline. */}},{critical});return map;
}
