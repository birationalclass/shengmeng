import * as THREE from 'three';
const pending=[];let started=false,running=0;
function pump(){while(started&&running<2&&pending.length){running++;pending.shift()().finally(()=>{running--;pump();});}}
export function startDeferredTextures(){started=true;pump();}
export function deferredTexture(url){
 const canvas=document.createElement('canvas');canvas.width=canvas.height=1;
 const ctx=canvas.getContext('2d');ctx.fillStyle=/normal|waternormals/.test(url)?'rgb(128,128,255)':'white';ctx.fillRect(0,0,1,1);
 const map=new THREE.CanvasTexture(canvas);
 pending.push(async()=>{try{const loaded=await new THREE.TextureLoader().loadAsync(url);map.image=loaded.image;map.needsUpdate=true;loaded.dispose();}catch{/* Retain the neutral material if offline. */}});pump();return map;
}
