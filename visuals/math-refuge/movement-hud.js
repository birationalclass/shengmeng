// World units are metres. Measure translation, not keyboard state or rotation.
export function createMovementHud(hint,dial){
 const ticks=dial.querySelector('.speed-ticks'),needle=dial.querySelector('.speed-needle'),value=dial.querySelector('.speed-value');
 for(let i=0;i<=16;i++){
  const a=(-112.5+i*225/16)*Math.PI/180,r=i%4?53:49;
  const line=document.createElementNS('http://www.w3.org/2000/svg','line');
  for(const [k,v] of Object.entries({x1:80+Math.sin(a)*r,y1:56-Math.cos(a)*r,x2:80+Math.sin(a)*58,y2:56-Math.cos(a)*58}))line.setAttribute(k,v);
  ticks.append(line);
 }
 let wasLocked=false,noticeAge=0,speed=0,still=0;
 return {
  hint(remaining,dt){
   if(remaining){wasLocked=true;noticeAge=0;}else noticeAge+=dt;
   hint.hidden=false;
   hint.textContent=remaining?`开场运镜 · ${remaining} 秒后可操作镜头`:'镜头已解锁 · 拖动观察，滚轮前后移动';
   hint.style.opacity=remaining||noticeAge<2.5?'.62':'0';
   if(wasLocked&&!remaining){wasLocked=false;noticeAge=0;}
  },
  update(metresPerSecond,dt,manual){
   const target=manual&&Number.isFinite(metresPerSecond)?metresPerSecond*3.6:0;
   speed+=(target-speed)*(1-Math.exp(-dt/.25));
   still=target<.15?still+dt:0;
   const visible=manual&&noticeAge>3.3&&still<.65&&speed>.2;
   dial.classList.toggle('is-moving',visible);dial.setAttribute('aria-hidden',String(!visible));
   value.textContent=String(Math.round(speed));
   needle.style.transform=`rotate(${-112.5+225*Math.min(speed/80,1)}deg)`;
  }
 };
}
