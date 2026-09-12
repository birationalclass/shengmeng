import {fitDiagramSurface} from './diagram-viewport.js?v=67';
import {visualMotion} from './visual-style.js?v=41';
import {createStabilityProof} from './stability-proof.js?v=112';

export const stabilityExamples=Object.freeze([{p:1,q:1,r:3},{p:0,q:0,r:2},{p:1,q:0,r:2}]);
// All positions share one coordinate map. Negative indices, not a display edge,
// are the reason the two endpoint spaces vanish.
const point=(p,q)=>[260+100*p,322-68*q];
const clamp=x=>Math.max(0,Math.min(1,x)),smooth=x=>{x=clamp(x);return x*x*(3-2*x);};
const mix=(a,b,t)=>a.map((x,i)=>x+(b[i]-x)*t);
const segment=(a,b,ha,hb)=>{
 const d=b.map((v,i)=>v-a[i]),edge=h=>Math.min(h[0]/Math.abs(d[0]),h[1]/Math.abs(d[1]));
 return `M${mix(a,b,edge(ha)).join(',')} L${mix(b,a,edge(hb)).join(',')}`;
};
export function createStabilityView({viewport,board,controls,math,language}){
 const R=String.raw,t=(zh,en)=>language()==='en'?en:zh;
 const host=document.createElement('div');host.id='stabilityView';host.inert=true;host.setAttribute('aria-hidden','true');viewport.append(host);
 const toolbar=document.createElement('nav');toolbar.id='stabilityControls';toolbar.hidden=true;controls.append(toolbar);
 let active=false,context=null,exampleIndex=0,key='',scene=null,mode='outgoing',frame=0,run=0,sceneSerial=0;
 const proof=createStabilityProof({board,math,language,onSelect:mode=>selectMode(mode,false)});
 const label=(x,y,tex,width=120,cls='')=>`<span class="stability-label ${cls}" style="left:${x-width/2}px;top:${y-20}px;width:${width}px">${math(tex)}</span>`;
 const current=()=>stabilityExamples[exampleIndex];
 function diagnostic(phase='idle'){
  const {p,q,r}=current();window.spectralStability={active,exampleIndex,p,q,r,mode,phase,source:[p-r,q+r-1],target:[p+r,q-r+1],centralTermPresent:!!scene?.querySelector('[data-central]')};
 }
 function cancel(){
  run++;cancelAnimationFrame(frame);frame=0;
  for(const el of host.querySelectorAll('.stability-trace')){
   const opacity=getComputedStyle(el).opacity;
   if(visualMotion().reduced)el.remove();else el.animate([{opacity},{opacity:0}],{duration:visualMotion().exit,fill:'forwards'}).finished.then(()=>el.remove(),()=>el.remove());
  }
 }
 function draw(){
  cancel();const e=current(),{p,q,r}=e,source=point(p-r,q+r-1),center=point(p,q),target=point(p+r,q-r+1);
  const previous=scene,fid=`stability-flow-${++sceneSerial}`;scene=document.createElement('div');scene.className='stability-scene';scene.dataset.flowId=fid;
  let svg=`<defs><marker id="stability-tip" markerUnits="userSpaceOnUse" markerWidth="9" markerHeight="9" refX="7" refY="4.5" orient="auto"><path d="M1.5,1.5 L7,4.5 L1.5,7.5" fill="none" stroke="currentColor" stroke-width="1.3"/></marker><linearGradient id="${fid}" gradientUnits="userSpaceOnUse"><stop stop-color="#f4d89b" stop-opacity="0"/><stop stop-color="#f4d89b" stop-opacity=".75"/><stop stop-color="#fff0bd"/><stop stop-color="#f4d89b" stop-opacity=".75"/><stop stop-color="#f4d89b" stop-opacity="0"/></linearGradient></defs><path class="stability-axis" d="M24,322 H792 M260,432 V18"/>`,labels=label(75,25,`E_${r}`,100,'page-title')+label(560,15,R`p=${p},\quad q=${q},\quad r=${r}`,360,'parameters')+label(805,322,'i',25,'axis')+label(244,17,'j',25,'axis');
  for(let i=0;i<=4;i++)for(let j=0;j<=4;j++){
   const [x,y]=point(i,j),central=i===p&&j===q;
   svg+=`<rect class="stability-node ${central?'central':''}" ${central?'data-central':''} data-p="${i}" data-q="${j}" x="${x-40}" y="${y-18}" width="80" height="36" rx="8"/>`;
   labels+=label(x,y,`E_${r}^{${i},${j}}`,78,central?'central':'context');
  }
  for(const [name,pos,indices] of [['incoming',source,[p-r,q+r-1]],['outgoing',target,[p+r,q-r+1]]]){
   svg+=`<rect class="stability-zero-space" data-zero-end="${name}" data-p="${indices[0]}" data-q="${indices[1]}" x="${pos[0]-53}" y="${pos[1]-22}" width="106" height="44" rx="9"/>`;
   labels+=label(pos[0],pos[1],`0`,70,'zero')+label(pos[0],pos[1]-40,`E_${r}^{${indices.join(',')}}`,120,'zero-name');
  }
  const paths={incoming:segment(source,center,[58,26],[45,23]),outgoing:segment(center,target,[45,23],[58,26])};
  svg+=`<path class="stability-map incoming" data-map="incoming" data-source="${p-r},${q+r-1}" data-target="${p},${q}" d="${paths.incoming}" marker-end="url(#stability-tip)"/><path class="stability-map outgoing" data-map="outgoing" data-source="${p},${q}" data-target="${p+r},${q-r+1}" d="${paths.outgoing}" marker-end="url(#stability-tip)"/>`;
  labels+=label((source[0]+center[0])/2,(source[1]+center[1])/2-19,`d_${r}`,60,'map')+label((center[0]+target[0])/2,(center[1]+target[1])/2-19,`d_${r}`,60,'map');
  labels+=label(60,342,'-2',35,'axis')+label(160,342,'-1',35,'axis')+label(243,394,'-1',35,'axis');
  const stable=context.step===1?R`E_\infty^{${p},${q}}:=E_{${r}}^{${p},${q}}`:R`E_{${r}}^{${p},${q}}\xrightarrow{\sim}E_{${r+1}}^{${p},${q}}\xrightarrow{\sim}\cdots`;
  labels+=`<div class="stability-result" style="left:250px;top:411px;width:490px">${math(stable)}</div>`;
  scene.innerHTML=`<svg viewBox="0 0 840 525" role="img" aria-label="${t('第一象限中的入射与出射零微分','Zero incoming and outgoing differentials in the first quadrant')}">${svg}</svg>${labels}`;
  host.append(scene);if(previous){previous.setAttribute('aria-hidden','true');if(visualMotion().reduced)previous.remove();else previous.animate([{opacity:getComputedStyle(previous).opacity},{opacity:0}],{duration:visualMotion().exit,fill:'forwards'}).finished.then(()=>previous.remove(),()=>previous.remove());}
  if(!visualMotion().reduced)scene.animate([{opacity:0},{opacity:1}],{duration:visualMotion().enter,easing:visualMotion().easing});
  updateMode();diagnostic();
 }

 function updateMode(){
  if(!scene)return;scene.dataset.mode=mode;
  for(const path of scene.querySelectorAll('[data-map]'))path.classList.toggle('is-emphasized',mode==='stable'||path.dataset.map===mode);
  toolbar.querySelectorAll('[data-stability-mode]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.stabilityMode===mode)));
 }
 function animate(which){
  cancel();if(!active||!scene||context.step===0&&context.notePage<2||which==='stable'){diagnostic();return;}
  if(visualMotion().reduced){diagnostic('zero');return;}
  const id=run,{p,q,r}=current(),a=which==='outgoing'?point(p,q):point(p-r,q+r-1),b=which==='outgoing'?point(p+r,q-r+1):point(p,q);
  const path=scene.querySelector(`[data-map="${which}"]`),svg=scene.querySelector('svg'),ns='http://www.w3.org/2000/svg',trace=document.createElementNS(ns,'g');trace.classList.add('stability-trace');trace.setAttribute('aria-hidden','true');
  const glow=document.createElementNS(ns,'path');glow.setAttribute('d',path.getAttribute('d'));glow.setAttribute('class','stability-flow');glow.setAttribute('stroke',`url(#${scene.dataset.flowId})`);
  const particle=document.createElementNS(ns,'g'),dot=document.createElementNS(ns,'circle'),zero=document.createElementNS(ns,'text');dot.setAttribute('r','7');dot.setAttribute('class','stability-particle');zero.textContent='0';zero.setAttribute('class','stability-moving-zero');zero.setAttribute('text-anchor','middle');zero.setAttribute('dominant-baseline','central');particle.append(dot,zero);trace.append(glow,particle);svg.append(trace);
  const gradient=scene.querySelector(`#${scene.dataset.flowId}`);for(const [k,v] of Object.entries({x1:a[0],y1:a[1],x2:b[0],y2:b[1]}))gradient.setAttribute(k,v);
  const motion=visualMotion(),duration=motion.emphasis*4+motion.hold+motion.exit,start=performance.now();
  const tick=now=>{
   if(id!==run||!active||!trace.isConnected)return;const u=clamp((now-start)/duration),travel=smooth(u/.62),xy=mix(a,b,travel),fade=smooth(u/.08)*(1-smooth((u-.87)/.13));
   particle.setAttribute('transform',`translate(${xy.join(' ')})`);particle.style.opacity=fade;
   // A nonzero representative is shown only on the outgoing route. The
   // incoming route transports an actual zero symbol from its zero source.
   const shrinking=1-smooth((u-.62)/.12),growing=smooth((u-.71)/.12);
   dot.setAttribute('r',String(which==='outgoing'?7*shrinking:0));zero.style.opacity=which==='incoming'?'1':String(growing);zero.style.fontSize=`${which==='incoming'?22:22*growing}px`;
   glow.style.opacity=fade;[...gradient.children].forEach((stop,i)=>stop.setAttribute('offset',String(clamp(travel+[-.24,-.12,0,.08,.18][i]))));
   diagnostic(u<.62?'travel':u<.83?'zero':'settling');if(u<1)frame=requestAnimationFrame(tick);else{trace.remove();frame=0;diagnostic('complete');}
  };tick(start);
 }
 function paintControls(){
  toolbar.innerHTML=`<div class="stability-buttons">${[['outgoing',t('出射','Outgoing')],['incoming',t('入射','Incoming')],['stable',t('稳定','Stable')]].map(([v,name])=>`<button data-stability-mode="${v}" aria-pressed="${mode===v}">${name}${v==='stable'?'':' '+math(`d_${current().r}`)}</button>`).join('')}<button data-stability-replay aria-label="${t('重播当前路径','Replay the current path')}">↻</button></div><label class="stability-example-picker">${t('例子','Example')} <select id="stabilityExample">${stabilityExamples.map((e,i)=>`<option value="${i}" ${i===exampleIndex?'selected':''}>p = ${e.p}, q = ${e.q}, r = ${e.r}</option>`).join('')}</select></label>`;
 }
 function selectMode(next,play=true){mode=next;proof.selectMode(mode);updateMode();if(play)animate(mode);else diagnostic();}
 toolbar.addEventListener('click',e=>{if(!active)return;const b=e.target.closest('[data-stability-mode],[data-stability-replay]');if(!b)return;selectMode(b.dataset.stabilityMode||mode,true);});
 toolbar.addEventListener('change',e=>{if(!active||e.target.id!=='stabilityExample')return;exampleIndex=Number(e.target.value);draw();paintControls();proof.render({state:context,example:current()});animate(mode);});
 const fit=()=>fitDiagramSurface(viewport,host,'--stability-scale');new ResizeObserver(fit).observe(viewport);
 return {play:()=>animate(mode),clear:cancel,isPlaying:()=>frame!==0,sync(s){
  const was=active,expositionOnly=!s.cover&&s.module==='converge'&&s.step===0&&s.notePage<2;active=!s.cover&&s.module==='converge'&&s.step<=1&&!expositionOnly;context=s;host.classList.toggle('is-active',active);host.inert=!active;host.setAttribute('aria-hidden',String(!active));toolbar.hidden=!active||s.step===0&&s.notePage<2;viewport.classList.toggle('has-stability-view',active);
  if(!active){if(was)cancel();key='';proof.render(expositionOnly?{state:s,example:current()}:null);diagnostic();return;}
  const next=[s.step,s.notePage,language()].join(':');if(next!==key){key=next;proof.render({state:s,example:current()});mode=proof.mode();draw();paintControls();}else proof.render({state:s,example:current()});fit();
 }};
}
