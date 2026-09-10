import {visualMotion} from './visual-style.js?v=40';
// A finite, user-triggered trace of an element under two consecutive differentials.
export function createSquareTrace(host){
 const ns='http://www.w3.org/2000/svg';let layer=null,frame=0,current=null,running=false,currentCentres=null,serial=0,finished=null,resolveFinished=null;
 const reduced=matchMedia('(prefers-reduced-motion:reduce)');
 const clear=()=>{resolveFinished?.(false);resolveFinished=null;host.querySelectorAll('[data-element-focus]').forEach(el=>el.removeAttribute('data-element-focus'));cancelAnimationFrame(frame);if(layer){const retiring=layer;retiring.removeAttribute('id');if(reduced.matches)retiring.remove();else{const fade=retiring.animate([{opacity:getComputedStyle(retiring).opacity},{opacity:0}],{duration:visualMotion().exit,easing:visualMotion().easing,fill:'forwards'});fade.finished.then(()=>retiring.remove(),()=>retiring.remove());}}layer=null;current=null;running=false;};
 const sync=(effect,enabled)=>{if(!enabled||!['square1','square2'].includes(effect)||effect!==current)clear();};
 const play=(effect,centres)=>{
  if(running&&current===effect)return finished;
  clear();current=effect;currentCentres=centres;running=true;
  finished=new Promise(resolve=>{resolveFinished=resolve;});
  const complete=()=>{running=false;resolveFinished?.(true);resolveFinished=null;};
  const horizontal=effect==='square1',color=horizontal?'#f4ce86':'#c9b5ff',delta=horizontal?'δ₁':'δ₂';
  const [[x0,y0],[x1,y1],[x2,y2]]=centres,ux=horizontal?1:0,uy=horizontal?0:-1,pad=horizontal?39:24;
  layer=document.createElementNS(ns,'svg');layer.id='elementTrace';layer.classList.add('element-trace-layer');layer.setAttribute('viewBox','0 0 840 525');layer.setAttribute('role','img');layer.setAttribute('aria-label',`a → ${delta}(a) → 0`);layer.dataset.concept=effect;
  const gradientId=`element-sweep-${++serial}`;
  layer.innerHTML=`<defs><linearGradient id="${gradientId}" gradientUnits="userSpaceOnUse"><stop offset="0" stop-color="${color}" stop-opacity="0"/><stop offset=".5" stop-color="${color}" stop-opacity=".4"/><stop offset=".8" stop-color="${color}"/><stop offset="1" stop-color="${color}" stop-opacity="0"/></linearGradient></defs><g class="element-flow" fill="none" stroke="url(#${gradientId})" stroke-width="2.8" stroke-linecap="round">${centres.slice(0,2).map(([x,y],i)=>`<path d="M${x+ux*pad},${y+uy*pad} L${centres[i+1][0]-ux*pad},${centres[i+1][1]-uy*pad}"/>`).join('')}</g><g class="element-token"><circle class="element-dot" r="7" fill="${color}" stroke="#fff9" stroke-width=".7"/><text class="element-zero" x="0" y="1" text-anchor="middle" dominant-baseline="central" fill="${color}" stroke="#10252e" stroke-width="4" paint-order="stroke" font-family="KaTeX_Main,Georgia,serif" font-size="27">0</text></g>`;
  host.append(layer);
  const token=layer.querySelector('.element-token'),dot=layer.querySelector('.element-dot'),zero=layer.querySelector('.element-zero'),gradient=layer.querySelector('linearGradient'),flow=layer.querySelector('.element-flow');
  const labels=centres.map(([x,y])=>[...host.querySelectorAll('.term-label')].find(el=>Math.abs(parseFloat(el.style.left)+parseFloat(el.style.width)/2-x)<.1&&Math.abs(parseFloat(el.style.top)+parseFloat(el.style.height)/2-y)<.1));
  const clamp=t=>Math.max(0,Math.min(1,t)),ease=t=>{t=clamp(t);return t*t*(3-2*t);};
  const draw=t=>{
   let x=x0,y=y0,phase='appear';
   if(t>=160&&t<820){const u=ease((t-160)/660);x=x0+(x1-x0)*u;y=y0+(y1-y0)*u;phase='first-arrow';}
   else if(t>=820&&t<1020){x=x1;y=y1;phase='middle';}
   else if(t>=1020){const u=ease((t-1020)/660);x=x1+(x2-x1)*u;y=y1+(y2-y1)*u;phase=t<1680?'second-arrow':t<1870?'shrink':t<2230?'zero-morph':'complete';}
   labels.forEach((label,i)=>{if(label)label.dataset.elementFocus=String(Math.abs(x-centres[i][0])<=34&&Math.abs(y-centres[i][1])<=19);});
   const shrink=ease((t-1680)/190),morph=ease((t-1870)/360);
   token.setAttribute('transform',`translate(${x} ${y})`);dot.setAttribute('r',String(7*(1-shrink)+.8*shrink));dot.setAttribute('opacity',String(ease(t/160)*(1-morph)));
   zero.setAttribute('opacity',String(morph));zero.setAttribute('transform',`scale(${.06+.94*morph} ${.06+.94*morph})`);
   gradient.setAttribute('x1',x-38*ux);gradient.setAttribute('y1',y-38*uy);gradient.setAttribute('x2',x+18*ux);gradient.setAttribute('y2',y+18*uy);flow.setAttribute('opacity',String(t<1680?1:1-shrink));layer.dataset.phase=phase;
  };
  if(reduced.matches){draw(2230);complete();return finished;}
  const start=performance.now();draw(0);
  const tick=now=>{const elapsed=now-start;draw(elapsed);if(elapsed<2230)frame=requestAnimationFrame(tick);else complete();};frame=requestAnimationFrame(tick);return finished;
 };
 reduced.addEventListener('change',e=>{if(e.matches&&running){const effect=current,centres=currentCentres;clear();play(effect,centres);}});
 return {clear,sync,play};
}
