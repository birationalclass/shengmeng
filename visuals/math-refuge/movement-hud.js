import {horizontalSpeedLimit,AltitudeDialRange} from './altitude-speed.js';
// World units are metres. Measure translation, not keyboard state or rotation.
export function createMovementHud(hint,dial){
 const ticks=dial.querySelector('.speed-ticks'),needle=dial.querySelector('.speed-needle'),value=dial.querySelector('.speed-value');
 for(let i=0;i<=28;i++){
  const a=(-112.5+i*225/28)*Math.PI/180,r=i%4?53:49;
  const line=document.createElementNS('http://www.w3.org/2000/svg','line');
  for(const [k,v] of Object.entries({x1:80+Math.sin(a)*r,y1:56-Math.cos(a)*r,x2:80+Math.sin(a)*58,y2:56-Math.cos(a)*58}))line.setAttribute(k,v);
  ticks.append(line);
 }
 const range=new AltitudeDialRange(),labels=[];
 for(const [x,anchor] of [[20,'start'],[140,'end']]){
  const label=document.createElementNS('http://www.w3.org/2000/svg','text');
  label.setAttribute('x',x);label.setAttribute('y',90);label.setAttribute('text-anchor',anchor);label.setAttribute('font-size','9');label.setAttribute('fill','currentColor');
  dial.querySelector('svg').append(label);labels.push(label);
 }
 let previousMax=0;
 let wasLocked=false,noticeAge=0,speed=0;
 return {
  hint(remaining,dt){
   if(remaining){wasLocked=true;noticeAge=0;}else noticeAge+=dt;
   hint.hidden=false;
   hint.textContent=remaining?`开场运镜 · ${remaining} 秒后可操作镜头`:'镜头已解锁 · 拖动观察，滚轮前后移动';
   hint.style.opacity=remaining||noticeAge<2.5?'.62':'0';
   if(wasLocked&&!remaining){wasLocked=false;noticeAge=0;}
  },
  update(metresPerSecond,dt,manual,height=0){
   const bounds=range.update(horizontalSpeedLimit(height),dt);
   if(bounds.max!==previousMax){previousMax=bounds.max;labels.forEach((label,i)=>{label.textContent=String(i?bounds.max:bounds.min);label.animate?.([{opacity:0},{opacity:1}],{duration:550,fill:"both"});});}
   dial.dataset.rangeMin=String(bounds.min);dial.dataset.rangeMax=String(bounds.max);
   const target=manual&&Number.isFinite(metresPerSecond)?metresPerSecond*3.6:0;
   speed+=(target-speed)*(1-Math.exp(-dt/.25));
   const visible=manual&&noticeAge>3.3&&speed>20;
   dial.classList.toggle('is-moving',visible);dial.setAttribute('aria-hidden',String(!visible));
   value.textContent=String(Math.max(0,Math.round(speed)));
   needle.style.transform=`rotate(${-112.5+225*Math.max(0,Math.min((speed-bounds.displayMin)/(bounds.displayMax-bounds.displayMin),1))}deg)`;
  }
 };
}
