// Finite demonstrations. The degree is always an integer in mathematical labels;
// only the grouping outline interpolates between successive layouts.
export function createDegreeSweep({diagram,read,write,outline,line}){
 let serial=0,frame=0,resolveFrame=null,running=false,target=null,history=[];
 const reduced=()=>matchMedia('(prefers-reduced-motion:reduce)').matches;
 function publish(){window.spectralDegreeSweep={running,target,history:[...history]};}
 function stop(){serial++;cancelAnimationFrame(frame);resolveFrame?.();resolveFrame=null;running=false;publish();}
 const pause=ms=>new Promise(resolve=>setTimeout(resolve,ms));
 const morph=(from,to)=>new Promise(resolve=>{
  const path=diagram.querySelector('.diag-box'),connector=diagram.querySelector('.diag');
  if(!path||reduced()){resolve();return;}
  resolveFrame=resolve;const start=performance.now(),duration=480;
  const tick=now=>{const t=Math.min(1,(now-start)/duration),u=t*t*(3-2*t),n=from+(to-from)*u;path.setAttribute('d',outline(n));connector?.setAttribute('d',line(n));if(t<1)frame=requestAnimationFrame(tick);else{resolveFrame=null;resolve();}};
  tick(start);
 });
 async function play(force=false){
  if(running&&!force)return;
  stop();const run=serial;running=true;history=[];
  for(let n=0;n<=4;n++){
   const from=n===0?0:n-1;target=n;history.push(n);write(n);publish();
   await morph(from,n);if(run!==serial)return;
   await pause(reduced()?380:500);if(run!==serial)return;
  }
  running=false;publish();
 }
 return {play,stop,sync(enabled){if(running&&(!enabled||read()!==target))stop();}};
}

// Total differential: different K-summands are added only after embedding in C.
// D²: the mixed terms cancel in the same K; the pure terms vanish separately.
export function createTotalTrace({host,math,point,degree}){
 const ns='http://www.w3.org/2000/svg';let layer=null,caption=null,frame=0,kind=null,running=false,token=0;
 const reduced=()=>matchMedia('(prefers-reduced-motion:reduce)').matches;
 const mix=(a,b,t)=>a.map((x,i)=>x+(b[i]-x)*t),clamp=x=>Math.max(0,Math.min(1,x)),ease=x=>{x=clamp(x);return x*x*(3-2*x);};
 function clear(){
  token++;cancelAnimationFrame(frame);running=false;kind=null;host.querySelectorAll('[data-total-focus]').forEach(el=>el.removeAttribute('data-total-focus'));
  for(const old of[layer,caption].filter(Boolean)){old.removeAttribute('id');if(reduced())old.remove();else{const fade=old.animate([{opacity:getComputedStyle(old).opacity},{opacity:0}],{duration:250,easing:'ease-out',fill:'forwards'});fade.finished.then(()=>old.remove(),()=>{});}}
  layer=null;caption=null;
 }
 function play(effect,force=false){
  if(running&&kind===effect&&!force)return;
  clear();kind=effect;running=true;const run=token,n=degree(),p=Math.floor(n/2),q=n-p;
  const a=point(p,q),h=point(p+1,q),v=point(p,q+1),hh=point(p+2,q),m=point(p+1,q+1),vv=point(p,q+2),sum=[420,445];
  const isSquare=effect==='totalsquare',colors=['#71e2d0','#8fbeff','#71e2d0','#8fbeff'];
  layer=document.createElementNS(ns,'svg');layer.id='totalTrace';layer.classList.add('element-trace-layer','total-trace-layer');layer.setAttribute('viewBox','0 0 840 525');layer.dataset.kind=effect;layer.setAttribute('role','img');layer.setAttribute('aria-label',isSquare?'D squared: pure terms vanish and mixed terms cancel':'D: add both differential images in the total complex');
  layer.innerHTML=`<g class="total-flow" fill="none" stroke-width="2.7" stroke-linecap="round">${[ [a,h],[a,v],...(isSquare?[[h,hh],[h,m],[v,m],[v,vv]]:[]) ].map(([s,t],i)=>{const d=Math.hypot(t[0]-s[0],t[1]-s[1]),pad=s[0]===t[0]?24:39;return `<path d="M${s[0]+(t[0]-s[0])*pad/d},${s[1]+(t[1]-s[1])*pad/d} L${t[0]-(t[0]-s[0])*pad/d},${t[1]-(t[1]-s[1])*pad/d}" stroke="${i%2?colors[1]:colors[0]}" opacity="0"/>`;}).join('')}</g>${Array.from({length:isSquare?4:2},(_,i)=>`<circle class="total-dot" r="7" fill="${colors[i]}" stroke="#effaf799" stroke-width=".7"/>`).join('')}${(isSquare?[hh,m,vv]:[sum]).map(([x,y])=>`<text class="total-zero" x="${x}" y="${y+1}" text-anchor="middle" dominant-baseline="central" fill="#f4d08c" stroke="#10252e" stroke-width="4" paint-order="stroke" font-family="KaTeX_Main,Georgia,serif" font-size="28" opacity="0">0</text>`).join('')}`;
  host.append(layer);
  caption=document.createElement('div');caption.id='totalTraceCaption';caption.className='diagram-math-layer total-trace-caption';
  caption.innerHTML=`<div class="total-demo-label" style="left:55px;top:405px;width:730px">${math(`a\\in K^{${p},${q}}\\subseteq C^{${n}}`)}</div><div class="total-demo-label total-demo-result" style="left:30px;top:455px;width:780px">${math(isSquare?`D^2a=0\\in C^{${n+2}}`:`Da=\\delta_1a+\\delta_2a\\in C^{${n+1}}`)}</div>`;host.append(caption);
  const dots=[...layer.querySelectorAll('.total-dot')],flows=[...layer.querySelectorAll('.total-flow path')],zeros=[...layer.querySelectorAll('.total-zero')],result=caption.querySelector('.total-demo-result');
  const dot=(i,pos,opacity=1,r=7)=>{dots[i].setAttribute('cx',pos[0]);dots[i].setAttribute('cy',pos[1]);dots[i].setAttribute('opacity',opacity);dots[i].setAttribute('r',r);};
  const glow=(el,t,start,duration)=>{const u=clamp((t-start)/duration);el.setAttribute('opacity',u>0&&u<1?Math.sin(Math.PI*u):0);};
  function draw(t){
   const first=ease((t-180)/760);flows.forEach((el,i)=>glow(el,t,i<2?180:1250,760));
   if(!isSquare){
    const gather=ease((t-1350)/820),fade=ease((t-2170)/400);
    dot(0,mix(mix(a,h,first),[sum[0]-30*(1-fade),sum[1]],gather),ease(t/180)*(1-fade));
    dot(1,mix(mix(a,v,first),[sum[0]+30*(1-fade),sum[1]],gather),ease(t/180)*(1-fade));
    // The result is typeset in C^{n+1}, outside every K-term.
    result.style.opacity=String(fade);zeros[0].setAttribute('opacity',0);
   }else{
    const second=ease((t-1250)/760),collapse=ease((t-2120)/470),cross=24*(1-collapse);
    if(t<1250){dot(0,mix(a,h,first),ease(t/180));dot(1,mix(a,v,first),ease(t/180));dot(2,a,0);dot(3,a,0);}
    else{
     dot(0,mix(h,hh,second),1-collapse,7*(1-collapse));dot(3,mix(v,vv,second),1-collapse,7*(1-collapse));
     dot(2,mix(h,[m[0]-cross,m[1]],second),(1-collapse)*ease((t-1250)/120));dot(1,mix(v,[m[0]+cross,m[1]],second),1-collapse);
    }
    zeros.forEach(z=>z.setAttribute('opacity',collapse));result.style.opacity=String(ease((t-2510)/400));
   }
   for(const label of host.querySelectorAll('.term-label')){
    const x=parseFloat(label.style.left)+parseFloat(label.style.width)/2,y=parseFloat(label.style.top)+parseFloat(label.style.height)/2;
    const focus=dots.some(d=>Number(d.getAttribute('opacity'))>.05&&Math.abs(Number(d.getAttribute('cx'))-x)<34&&Math.abs(Number(d.getAttribute('cy'))-y)<19)||isSquare&&zeros.some(z=>Number(z.getAttribute('opacity'))>.05&&Math.abs(Number(z.getAttribute('x'))-x)<34&&Math.abs(Number(z.getAttribute('y'))-y)<19);
    label.toggleAttribute('data-total-focus',focus);
   }
   layer.dataset.phase=t<940?'first-differential':t<1250?'summands':t<2120?'second-stage':t<2910?'combination':'complete';
  }
  if(reduced()){draw(3100);running=false;return;}
  const start=performance.now();draw(0);const tick=now=>{if(run!==token)return;draw(now-start);if(now-start<3100)frame=requestAnimationFrame(tick);else running=false;};frame=requestAnimationFrame(tick);
 }
 return {play,clear,sync(effect,enabled){if(layer&&(!enabled||effect!==kind))clear();}};
}
