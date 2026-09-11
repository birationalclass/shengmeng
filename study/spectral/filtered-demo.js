import {visualMotion} from './visual-style.js?v=41';

// A finite double complex realizing both demonstrations. Every nonzero map
// is listed; all remaining maps on these basis vectors are zero.
export const filteredExample={
 degrees:{alpha:[0,1],beta:[1,0],c:[0,2],u:[1,1],s:[1,1],b:[1,1],v:[2,0],w:[1,2],t:[2,1],z:[3,0]},
 delta1:{u:{t:1},v:{z:1}},
 delta2:{alpha:{c:1},beta:{b:1},s:{w:1},v:{t:-1}},
 Z:[{a:{u:1,v:1},image:{z:1},inside:true},{a:{u:1},image:{t:1},inside:false},{a:{s:1},image:{w:1},inside:false},{a:{u:2,v:2},image:{z:2},inside:true}],
 B:[{a:{beta:1},image:{b:1},inside:true},{a:{alpha:1},image:{c:1},inside:false},{a:{alpha:1,beta:1},image:{c:1,b:1},inside:false},{a:{beta:2},image:{b:2},inside:true}]
};

// D acts on total cochains. Points along a grouping line represent whole
// cochains, not individual K components, and the tracks are not delta arrows.
export function createFilteredDemo({host,point,math}){
 const ns='http://www.w3.org/2000/svg';let layer=null,labels=null,frame=0,serial=0,key='';
 const clamp=t=>Math.max(0,Math.min(1,t)),ease=t=>{t=clamp(t);return t*t*(3-2*t);};
 const mix=(a,b,t)=>a.map((x,i)=>x+(b[i]-x)*t);
 function clear(){
  serial++;cancelAnimationFrame(frame);key='';host.querySelectorAll('[data-filtered-focus]').forEach(el=>el.removeAttribute('data-filtered-focus'));
  for(const old of[layer,labels].filter(Boolean)){old.removeAttribute('id');const m=visualMotion();if(m.reduced)old.remove();else{const fade=old.animate([{opacity:getComputedStyle(old).opacity},{opacity:0}],{duration:m.exit,easing:m.easing,fill:'forwards'});fade.finished.then(()=>old.remove(),()=>old.remove());}}
  layer=labels=null;
 }
 function play(topic,force=false){
  if(key===topic&&!force)return;clear();key=topic;const run=serial;
  const Z=topic==='Z',source=Z?[point(1,1),point(2,0)]:[point(0,1),point(1,0)];
  const inside=Z?point(3,0):point(1,1),out1=Z?point(2,1):point(0,2),out2=Z?point(1,2):mix(point(0,2),point(1,1),.5);
  const destinations=[[inside[0]-7,inside[1]-3],out1,out2,[inside[0]+7,inside[1]+3]];
  layer=document.createElementNS(ns,'svg');layer.id='filteredTrace';layer.classList.add('element-trace-layer','filtered-trace-layer');layer.setAttribute('viewBox','0 0 840 525');layer.dataset.topic=topic;layer.setAttribute('role','img');layer.setAttribute('aria-label',Z?'Test total cochains: their D images must lie in F cubed C cubed':'Boundary representatives: keep the D images lying in F one C squared');
  labels=document.createElement('div');labels.id='filteredTraceLabels';labels.className='diagram-label-plane filtered-trace-labels';labels.setAttribute('aria-hidden','true');
  const samples=filteredExample[topic].map((example,i)=>{
   const from=mix(...source,.34+i*.105),to=destinations[i],control=[(from[0]+to[0])/2+12*(i-1.5),(from[1]+to[1])/2-30-8*i];
   const track=document.createElementNS(ns,'path');track.setAttribute('d',`M${from} Q${control} ${to}`);track.setAttribute('fill','none');track.setAttribute('stroke',example.inside?'var(--blue)':'var(--gold)');track.setAttribute('stroke-width','1.1');track.setAttribute('opacity','0');layer.append(track);
   const circle=document.createElementNS(ns,'circle');circle.dataset.sample=i+1;circle.dataset.inside=example.inside;circle.setAttribute('r','4.3');circle.setAttribute('fill','var(--ink)');circle.setAttribute('stroke','var(--bg)');circle.setAttribute('stroke-width','1.4');layer.append(circle);
   const label=document.createElement('span');label.className='filtered-sample-label';label.innerHTML=`<span data-sample-source>${math(`${Z?'a':'b'}_${i+1}`)}</span><span data-sample-image style="opacity:0">${math(`D${Z?'a':'b'}_${i+1}`)}</span>`;labels.append(label);
   return {from,to,control,track,circle,label,example};
  });
  host.append(layer,labels);
  const draw=t=>{
   for(const [i,s] of samples.entries()){
    const u=ease((t-850-i*240)/1550),arrive=ease((t-2400-i*240)/420);
    const pos=s.from.map((x,k)=>(1-u)**2*x+2*(1-u)*u*s.control[k]+u*u*s.to[k]);
    s.circle.setAttribute('cx',pos[0]);s.circle.setAttribute('cy',pos[1]);s.circle.setAttribute('opacity',ease(t/300));
    s.circle.style.fill=arrive===0?'var(--ink)':`color-mix(in srgb, var(--ink) ${100*(1-arrive)}%, ${s.example.inside?'var(--blue)':'var(--gold)'})`;
    s.track.setAttribute('opacity',.32*Math.sin(Math.PI*u));
    s.label.style.left=`${pos[0]-25}px`;s.label.querySelector('[data-sample-source]').style.opacity=String(1-arrive);s.label.querySelector('[data-sample-image]').style.opacity=String(arrive);s.label.style.top=`${pos[1]+(i%2?8:-25)}px`;s.label.style.opacity=String(ease(t/300));s.label.style.color=s.example.inside&&arrive>0?'var(--blue)':!s.example.inside&&arrive>0?'var(--gold)':'var(--ink)';
   }
   for(const label of host.querySelectorAll('.diagram-label-plane:not(.filtered-trace-labels) .term-label')){
    const x=parseFloat(label.style.left)+parseFloat(label.style.width)/2,y=parseFloat(label.style.top)+parseFloat(label.style.height)/2;
    label.toggleAttribute('data-filtered-focus',samples.some(({circle})=>Math.abs(+circle.getAttribute('cx')-x)<34&&Math.abs(+circle.getAttribute('cy')-y)<19));
   }
   layer.dataset.phase=t<850?'representatives':t<3120?'images':t<3700?'membership':'complete';
  };
  const duration=3900;if(visualMotion().reduced){draw(duration);return;}
  const start=performance.now();draw(0);const tick=now=>{if(run!==serial)return;const t=visualMotion().reduced?duration:now-start;draw(t);if(t<duration)frame=requestAnimationFrame(tick);};frame=requestAnimationFrame(tick);
 }
 return {play,clear};
}
