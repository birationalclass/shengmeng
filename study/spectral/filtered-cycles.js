import {visualMotion} from './visual-style.js?v=41';
import {filteredExample} from './filtered-demo.js?v=92';

// Fixed example p=q=1, r=2. A dot is a whole total cochain, not a K-component.
// The outlined blue dots are samples in Z, not a picture of its entire vector space.
export function createFilteredCycles({host,point,math}){
 const ns='http://www.w3.org/2000/svg',R=String.raw;
 let layer=null,samples=[],outline=null,leader=null,caption=null,frame=0,generation=0,running=false,phase='absent',entrances=0,passes=0;
 const clamp=t=>Math.max(0,Math.min(1,t)),ease=t=>{t=clamp(t);return t*t*(3-2*t);},mix=(a,b,t)=>a.map((x,i)=>x+(b[i]-x)*t);
 const svg=(tag,attributes,parent)=>{const el=document.createElementNS(ns,tag);for(const [k,v]of Object.entries(attributes))el.setAttribute(k,v);parent.append(el);return el;};
 const publish=()=>{if(layer)layer.dataset.phase=phase;window.spectralCycles={phase,running,entrances,passes,p:1,q:1,r:2};};
 function cancel(){generation++;cancelAnimationFrame(frame);running=false;}
 function focus(){host.querySelectorAll('[data-filtered-focus]').forEach(e=>e.removeAttribute('data-filtered-focus'));for(const label of host.querySelectorAll('.term-label')){const x=parseFloat(label.style.left)+parseFloat(label.style.width)/2,y=parseFloat(label.style.top)+parseFloat(label.style.height)/2;label.toggleAttribute('data-filtered-focus',samples.some(({circle})=>Math.abs(+circle.getAttribute('cx')-x)<34&&Math.abs(+circle.getAttribute('cy')-y)<19));}}
 function position(s,pos){s.circle.setAttribute('cx',pos[0]);s.circle.setAttribute('cy',pos[1]);}
 function classified(){for(const s of samples){position(s,s.from);s.circle.setAttribute('opacity','1');s.circle.style.fill=s.example.inside?'var(--blue)':'var(--gold)';s.track.setAttribute('opacity','0');}for(const el of [outline,leader,caption])el.style.opacity='1';phase='classified';focus();publish();}
 function create(){
  if(layer)return;
  layer=document.createElement('div');layer.id='filteredCycles';layer.className='filtered-cycle-scene';layer.setAttribute('role','img');layer.setAttribute('aria-label','Samples of total cochains in F one C squared: blue samples belong to Z two one one');
  const canvas=svg('svg',{viewBox:'0 0 840 525'},layer),defs=svg('defs',{},canvas),marker=svg('marker',{id:'cycle-callout-tip',viewBox:'0 0 8 8',refX:6,refY:4,markerWidth:7,markerHeight:7,orient:'auto'},defs);svg('path',{d:'M1 1 L6 4 L1 7',fill:'none',stroke:'var(--blue)','stroke-width':1},marker);
  const source=[point(1,1),point(2,0)],inside=point(3,0),destinations=[[inside[0]-7,inside[1]-3],point(2,1),point(1,2),[inside[0]+7,inside[1]+3]],order=[0,2,3,1];
  samples=filteredExample.Z.map((example,i)=>{const from=mix(...source,.34+order[i]*.105),to=destinations[i],control=[(from[0]+to[0])/2+12*(i-1.5),(from[1]+to[1])/2-30-8*i];const track=svg('path',{d:`M${from} Q${control} ${to}`,fill:'none',stroke:example.inside?'var(--blue)':'var(--gold)','stroke-width':1.1,opacity:0},canvas);const circle=svg('circle',{'data-sample':i+1,'data-inside':example.inside,r:4.3,fill:'var(--gold)',stroke:'var(--bg)','stroke-width':1.4,opacity:0,cx:from[0],cy:from[1]},canvas);return{from,to,control,track,circle,example};});
  const a=samples[0].from,b=samples[3].from,length=Math.hypot(b[0]-a[0],b[1]-a[1]),angle=Math.atan2(b[1]-a[1],b[0]-a[0])*180/Math.PI,mid=mix(a,b,.5);
  outline=svg('rect',{x:a[0]-9,y:a[1]-9,width:length+18,height:18,rx:9,transform:`rotate(${angle} ${a[0]} ${a[1]})`,fill:'none',stroke:'var(--blue)','stroke-width':1,'stroke-dasharray':'3 3',opacity:0},canvas);
  leader=svg('path',{d:`M${mid[0]-5},${mid[1]+9} Q${mid[0]+10},390 350,414`,fill:'none',stroke:'var(--blue)','stroke-width':.9,'marker-end':'url(#cycle-callout-tip)',opacity:0},canvas);
  caption=document.createElement('div');caption.className='filtered-cycle-caption';caption.style.opacity='0';caption.innerHTML=math(R`Z_r^{p,q}\quad(p=1,\ q=1,\ r=2)`);layer.append(caption);host.append(layer);publish();
 }
 function timeline(duration,draw,complete){cancel();const run=generation;running=true;const start=performance.now();const tick=now=>{if(run!==generation)return;const t=visualMotion().reduced?duration:Math.min(duration,now-start);draw(t);if(t<duration)frame=requestAnimationFrame(tick);else{running=false;complete?.();}publish();};tick(start);}
 function enter(){entrances++;clear();create();phase='candidates';timeline(2100,t=>{for(const s of samples){s.circle.setAttribute('opacity',ease(t/400));const blue=s.example.inside?ease((t-650)/650):0;s.circle.style.fill=`color-mix(in srgb, var(--gold) ${100*(1-blue)}%, var(--blue))`;}outline.style.opacity=String(ease((t-1350)/400));leader.style.opacity=caption.style.opacity=String(ease((t-1650)/450));phase=t<650?'candidates':t<1350?'classification':'identification';},classified);}
 function play(){passes++;create();for(const el of [outline,leader,caption])el.style.opacity='1';const reset=phase==='images'||phase==='complete';phase='motion';timeline(4000,t=>{const fade=reset?1-ease(t/280):1;if(t<280&&reset){for(const s of samples){s.circle.setAttribute('opacity',fade);s.track.setAttribute('opacity','0');}return;}const elapsed=t-280;for(const [i,s]of samples.entries()){const u=ease((elapsed-250-i*170)/1700),pos=s.from.map((x,k)=>(1-u)**2*x+2*(1-u)*u*s.control[k]+u*u*s.to[k]);position(s,pos);s.circle.setAttribute('opacity',reset?ease(elapsed/280):1);s.circle.style.fill=s.example.inside?'var(--blue)':'var(--gold)';s.track.setAttribute('opacity',.35*Math.sin(Math.PI*u));}phase=elapsed<260?'classified':elapsed<2700?'images':'complete';focus();},()=>{phase='complete';publish();});}
 function stop(){cancel();if(!layer)return;const visible=samples.map(s=>+s.circle.getAttribute('opacity'));timeline(500,t=>{const hide=1-ease(t/240);if(t<240){samples.forEach((s,i)=>s.circle.setAttribute('opacity',visible[i]*hide));samples.forEach(s=>s.track.setAttribute('opacity','0'));}else{classified();samples.forEach(s=>s.circle.setAttribute('opacity',ease((t-240)/260)));}},classified);}
 function clear(){cancel();host.querySelectorAll('[data-filtered-focus]').forEach(e=>e.removeAttribute('data-filtered-focus'));const old=layer;layer=null;samples=[];phase='absent';if(old){old.removeAttribute('id');const m=visualMotion();if(m.reduced)old.remove();else old.animate([{opacity:getComputedStyle(old).opacity},{opacity:0}],{duration:m.exit,easing:m.easing,fill:'forwards'}).finished.then(()=>old.remove(),()=>old.remove());}publish();}
 return{enter,play,stop,clear,isPlaying:()=>running};
}
