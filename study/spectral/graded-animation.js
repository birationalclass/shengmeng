import {visualMotion} from './visual-style.js?v=41';

// All three tokens are classes in the same filtration-p quotient (in degrees
// n and n+1). The horizontal representative lies in F^{p+1}, hence its class
// is zero; the horizontal K-summand itself is not asserted to be zero.
export function createGradedTrace({host,point,read}) {
 const ns='http://www.w3.org/2000/svg';
 let layer=null,frame=0,serial=0,running=false,context='';
 const clamp=t=>Math.max(0,Math.min(1,t));
 const ease=t=>{t=clamp(t);return t*t*(3-2*t);};
 const mix=(a,b,t)=>a.map((x,i)=>x+(b[i]-x)*t);
 function clear(){
  serial++;cancelAnimationFrame(frame);running=false;
  host.querySelectorAll('[data-graded-focus]').forEach(el=>el.removeAttribute('data-graded-focus'));
  const old=layer;layer=null;if(!old)return;old.removeAttribute('id');
  const motion=visualMotion();if(motion.reduced){old.remove();return;}
  const fade=old.animate([{opacity:getComputedStyle(old).opacity},{opacity:0}],{duration:motion.exit,easing:motion.easing,fill:'forwards'});
  fade.finished.then(()=>old.remove(),()=>old.remove());
 }
 function play(force=false){
  if(running&&!force)return;
  clear();const {p,n}=read(),q=n-p;if(p>n||p<0)return;
  context=`${p}:${n}`;running=true;const run=serial,motion=visualMotion();
  const a=point(p,q),h=point(p+1,q),v=point(p,q+1);
  layer=document.createElementNS(ns,'svg');layer.id='gradedTrace';
  layer.classList.add('element-trace-layer','graded-trace-layer');
  layer.setAttribute('viewBox','0 0 840 525');layer.setAttribute('role','img');
  layer.setAttribute('aria-label','The class of a splits into the classes of its vertical and horizontal components; the horizontal class becomes zero in the filtration quotient.');
  layer.dataset.p=p;layer.dataset.q=q;layer.dataset.degree=n;
  const token=(name,color)=>`<g class="graded-token" data-token="${name}" color="${color}" opacity="0"><rect x="-25" y="-16" width="50" height="32" rx="7" fill="var(--bg)" stroke="currentColor" stroke-opacity=".8" stroke-width="1.1"/><path d="M-11,-9 H-15 V9 H-11 M11,-9 H15 V9 H11" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linecap="round"/><circle class="graded-dot" r="5" fill="currentColor"/><text class="graded-zero" x="0" y="0" text-anchor="middle" dominant-baseline="central" fill="currentColor" font-family="KaTeX_Main,Georgia,serif" font-size="22" opacity="0">0</text></g>`;
  const route=(target,color)=>{const vertical=a[0]===target[0],pad=vertical?24:39,d=Math.hypot(target[0]-a[0],target[1]-a[1]),s=mix(a,target,pad/d),t=mix(target,a,pad/d);return `<path d="M${s} L${t}" stroke="${color}" stroke-width="2.6" stroke-linecap="round" fill="none" opacity="0"/>`;};
  layer.innerHTML=`<g class="graded-flow">${route(h,'var(--teal)')}${route(v,'var(--blue)')}</g>${token('source','var(--gold)')}${token('horizontal','var(--teal)')}${token('vertical','var(--blue)')}`;
  host.append(layer);
  const source=layer.querySelector('[data-token=source]'),horizontal=layer.querySelector('[data-token=horizontal]'),vertical=layer.querySelector('[data-token=vertical]');
  const dot=horizontal.querySelector('.graded-dot'),zero=horizontal.querySelector('.graded-zero'),flows=[...layer.querySelectorAll('.graded-flow path')];
  const place=(el,position,opacity)=>{el.setAttribute('transform',`translate(${position})`);el.setAttribute('opacity',opacity);};
  function draw(t){
   const appear=ease(t/260),split=ease((t-500)/260),move=ease((t-620)/1100),vanish=ease((t-2080)/580);
   place(source,a,appear*(1-split));place(horizontal,mix(a,h,move),split);place(vertical,mix(a,v,move),split);
   dot.setAttribute('r',5*(1-vanish));dot.setAttribute('opacity',1-vanish);
   zero.setAttribute('opacity',vanish);zero.setAttribute('transform',`scale(${.2+.8*vanish})`);
   flows.forEach(el=>el.setAttribute('opacity',Math.sin(Math.PI*clamp((t-620)/1100))));
   for(const label of host.querySelectorAll('.term-label')){
    const x=parseFloat(label.style.left)+parseFloat(label.style.width)/2,y=parseFloat(label.style.top)+parseFloat(label.style.height)/2;
    const active=[[a,appear*(1-split)],[mix(a,h,move),split],[mix(a,v,move),split]].some(([pos,opacity])=>opacity>.05&&Math.abs(pos[0]-x)<34&&Math.abs(pos[1]-y)<19);
    label.toggleAttribute('data-graded-focus',active);
   }
   layer.dataset.phase=t<500?'source':t<1720?'component-images':t<2080?'target-classes':t<2800?'horizontal-zero':'complete';
  }
  const duration=3000;if(motion.reduced){draw(duration);running=false;return;}
  const start=performance.now();draw(0);
  const tick=now=>{if(run!==serial)return;const t=visualMotion().reduced?duration:now-start;draw(t);if(t<duration)frame=requestAnimationFrame(tick);else running=false;};
  frame=requestAnimationFrame(tick);
 }
 return {play,clear,sync(enabled){const {p,n}=read();if(layer&&(!enabled||context!==`${p}:${n}`))clear();}};
}
