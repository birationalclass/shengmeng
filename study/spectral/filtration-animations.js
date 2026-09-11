// Particle traces encode the support of component images, not dimensions or
// surjectivity: horizontal images increase i; vertical images preserve i.
import {visualMotion} from './visual-style.js?v=40';
export function createFiltrationTrace({host,point,read}){
 let layer=null,frame=0,run=0,active=false;
 function clear(){
  run++;cancelAnimationFrame(frame);active=false;
  if(!layer)return;
  const old=layer;layer=null;old.removeAttribute('id');
  const m=visualMotion();if(m.reduced){old.remove();return;}
  const a=old.animate([{opacity:getComputedStyle(old).opacity},{opacity:0}],{duration:m.exit,easing:m.easing,fill:'forwards'});
  a.finished.then(()=>old.remove(),()=>old.remove());
 }
 function play(force=false){
  if(active&&!force)return;clear();active=true;const token=run,{n,p}=read(),m=visualMotion(),particles=[];
  layer=document.createElementNS('http://www.w3.org/2000/svg','svg');layer.id='filtrationTrace';layer.classList.add('element-trace-layer','filtration-trace');layer.setAttribute('viewBox','0 0 840 525');layer.setAttribute('aria-label','Component images stay in the target filtration');layer.dataset.degree=n;layer.dataset.filtration=p;
  for(let i=Math.max(0,p);i<=n;i++)for(const direction of[1,2])for(let k=0;k<4;k++){
   const j=n-i,ti=i+(direction===1?1:0),tq=j+(direction===2?1:0),from=point(i,j),to=point(ti,tq);
   const circle=document.createElementNS('http://www.w3.org/2000/svg','circle');circle.setAttribute('r','3');circle.setAttribute('fill',direction===1?'var(--teal)':'var(--blue)');circle.setAttribute('stroke','var(--ink)');circle.setAttribute('stroke-width','.35');circle.dataset.source=`${i},${j}`;circle.dataset.target=`${ti},${tq}`;circle.setAttribute('opacity','0');layer.append(circle);
   const angle=(k/4)*Math.PI*2,offset=[6*Math.cos(angle),5*Math.sin(angle)];
   particles.push({circle,from,to,offset,delay:180+(i-p)*90+k*75});
  }
  host.append(layer);const ease=x=>{x=Math.max(0,Math.min(1,x));return x*x*(3-2*x)},end=particles.length?Math.max(...particles.map(x=>x.delay))+1550:650;
  function draw(t){
   particles.forEach(({circle,from,to,offset,delay})=>{
    const u=ease((t-delay)/1000),arrive=ease((t-delay-1050)/400);
    circle.setAttribute('cx',from[0]+(to[0]-from[0])*u+offset[0]);circle.setAttribute('cy',from[1]+(to[1]-from[1])*u+offset[1]);
    circle.setAttribute('opacity',.88*ease(t/180));circle.setAttribute('r',3-.8*arrive);
   });
   layer.dataset.phase=t>=end?'complete':t<180?'source':'migration';
  }
  if(m.reduced){draw(end);active=false;return;}
  const start=performance.now();draw(0);const tick=now=>{if(token!==run)return;draw(now-start);if(now-start<end)frame=requestAnimationFrame(tick);else active=false;};frame=requestAnimationFrame(tick);
 }
 return {play,clear,isPlaying:()=>active,sync(enabled){if(layer&&(!enabled||Number(layer.dataset.degree)!==read().n||Number(layer.dataset.filtration)!==read().p))clear();}};
}
