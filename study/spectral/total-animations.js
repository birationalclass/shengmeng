import {visualMotion} from './visual-style.js?v=40';
// Finite demonstrations. The degree is always an integer in mathematical labels;
// only the grouping outline interpolates between successive layouts.
export function createIndexedSweep({diagram,read,write,outline,line,values=()=>[0,1,2,3,4],publishName='spectralDegreeSweep'}){
 let serial=0,frame=0,resolveFrame=null,running=false,target=null,history=[];
 const reduced=()=>matchMedia('(prefers-reduced-motion:reduce)').matches;
 function publish(){window[publishName]={running,target,history:[...history]};}
 function stop(){serial++;cancelAnimationFrame(frame);resolveFrame?.();resolveFrame=null;running=false;publish();}
 const pause=ms=>new Promise(resolve=>setTimeout(resolve,ms));
 const morph=(from,to)=>new Promise(resolve=>{
  const path=diagram.querySelector('.diag-box'),connector=diagram.querySelector('.diag');
  if(!path||reduced()){resolve();return;}
  resolveFrame=resolve;const start=performance.now(),duration=visualMotion().emphasis;
  const tick=now=>{const t=Math.min(1,(now-start)/duration),u=t*t*(3-2*t),n=from+(to-from)*u;path.setAttribute('d',outline(n));connector?.setAttribute('d',line(n));if(t<1)frame=requestAnimationFrame(tick);else{resolveFrame=null;resolve();}};
  tick(start);
 });
 async function play(force=false){
  if(running&&!force)return;
  stop();const run=serial;running=true;history=[];
  const indices=values();
  for(let i=0;i<indices.length;i++){
   const n=indices[i],from=i===0?n:indices[i-1];target=n;history.push(n);write(n);publish();
   await morph(from,n);if(run!==serial)return;
   await pause(reduced()?380:visualMotion().hold);if(run!==serial)return;
  }
  running=false;publish();
 }
 return {play,stop,sync(enabled){if(running&&(!enabled||read()!==target))stop();}};
}

export const createDegreeSweep=options=>createIndexedSweep(options);

// Total differential: different K-summands are added only after embedding in C.
// D²: the mixed terms cancel in the same K; the pure terms vanish separately.
export function createTotalTrace({host,math,point,degree}){
 const ns='http://www.w3.org/2000/svg';let layer=null,caption=null,frame=0,kind=null,running=false,token=0;
 const reduced=()=>matchMedia('(prefers-reduced-motion:reduce)').matches;
 const mix=(a,b,t)=>a.map((x,i)=>x+(b[i]-x)*t),clamp=x=>Math.max(0,Math.min(1,x)),ease=x=>{x=clamp(x);return x*x*(3-2*x);};
 function clear(){
  token++;cancelAnimationFrame(frame);running=false;kind=null;host.querySelectorAll('[data-total-focus]').forEach(el=>el.removeAttribute('data-total-focus'));
  for(const old of[layer,caption].filter(Boolean)){old.removeAttribute('id');if(reduced())old.remove();else{const fade=old.animate([{opacity:getComputedStyle(old).opacity},{opacity:0}],{duration:visualMotion().exit,easing:visualMotion().easing,fill:'forwards'});fade.finished.then(()=>old.remove(),()=>{});}}
  layer=null;caption=null;
 }
 function play(effect,force=false){
  if(running&&kind===effect&&!force)return;
  clear();kind=effect;running=true;const isMixed=effect==='anticommute',run=token,n=isMixed?2:degree(),p=isMixed?1:Math.floor(n/2),q=isMixed?1:n-p;
  const a=point(p,q),h=point(p+1,q),v=point(p,q+1),hh=point(p+2,q),m=point(p+1,q+1),vv=point(p,q+2),sum=[420,445];
  // Pause on the incoming paths before their common endpoint. Addition and
  // zero use the target K tile centre, shared with the diagram geometry.
  const mixedStops=[[m[0],m[1]+14],[m[0]-14,m[1]]],additionCenter=m;
  const isSquare=effect==='totalsquare',colors=['var(--teal)','var(--blue)','var(--teal)','var(--blue)'];
  layer=document.createElementNS(ns,'svg');layer.id='totalTrace';layer.classList.add('element-trace-layer','total-trace-layer');layer.setAttribute('viewBox','0 0 840 525');layer.dataset.kind=effect;layer.setAttribute('role','img');layer.setAttribute('aria-label',isMixed?'The two mixed composites are opposite elements in the same target; their sum is zero':isSquare?'D squared: pure terms vanish and mixed terms cancel':'D: add both differential images in the total complex');
  layer.innerHTML=`<g class="total-flow" fill="none" stroke-width="2.7" stroke-linecap="round">${[ [a,h],[a,v],...(isMixed?[[h,m],[v,m]]:isSquare?[[h,hh],[h,m],[v,m],[v,vv]]:[]) ].map(([s,t],i)=>{const d=Math.hypot(t[0]-s[0],t[1]-s[1]),pad=s[0]===t[0]?24:39;return `<path d="M${s[0]+(t[0]-s[0])*pad/d},${s[1]+(t[1]-s[1])*pad/d} L${t[0]-(t[0]-s[0])*pad/d},${t[1]-(t[1]-s[1])*pad/d}" stroke="${s[0]===t[0]?colors[1]:colors[0]}" opacity="0"/>`;}).join('')}</g>${isSquare||isMixed?`<circle class="total-seed" cx="${a[0]}" cy="${a[1]}" r="7" fill="var(--gold)"/>`:""}${Array.from({length:isSquare?4:2},(_,i)=>`<circle class="total-dot" r="7" fill="${colors[i]}" stroke="#effaf799" stroke-width=".7"/>`).join('')}${isMixed?`<text class="total-plus" x="${additionCenter[0]}" y="${additionCenter[1]}" text-anchor="middle" dominant-baseline="central" fill="var(--gold)" font-family="KaTeX_Main,Georgia,serif" font-size="12" opacity="0">+</text>`:''}${(isMixed?[additionCenter]:isSquare?[hh,m,vv]:[sum]).map(([x,y])=>`<text class="total-zero" x="${x}" y="${y+(isMixed?0:1)}" text-anchor="middle" dominant-baseline="central" fill="var(--gold)" stroke="#10252e" stroke-width="4" paint-order="stroke" font-family="KaTeX_Main,Georgia,serif" font-size="28" opacity="0">0</text>`).join('')}`;
  host.append(layer);
  caption=document.createElement('div');caption.id='totalTraceCaption';caption.className='diagram-math-layer total-trace-caption';
  caption.innerHTML=`<div class="total-demo-label" style="left:55px;top:405px;width:730px">${math(isMixed?`a\\in K^{${p},${q}}`:`a\\in K^{${p},${q}}\\subseteq C^{${n}}`)}</div><div class="total-demo-label total-demo-result" style="left:30px;top:455px;width:780px">${math(isMixed?`\\delta_2\\delta_1a+\\delta_1\\delta_2a=0`:isSquare?`D^2a=0\\in C^{${n+2}}`:`Da=\\delta_1a+\\delta_2a\\in C^{${n+1}}`)}</div>`;host.append(caption);
  const plus=layer.querySelector('.total-plus');
  const seed=layer.querySelector('.total-seed'),dots=[...layer.querySelectorAll('.total-dot')],flows=[...layer.querySelectorAll('.total-flow path')],zeros=[...layer.querySelectorAll('.total-zero')],result=caption.querySelector('.total-demo-result');
  const dot=(i,pos,opacity=1,r=7)=>{dots[i].setAttribute('cx',pos[0]);dots[i].setAttribute('cy',pos[1]);dots[i].setAttribute('opacity',opacity);dots[i].setAttribute('r',r);};
  const glow=(el,t,start,duration)=>{const u=clamp((t-start)/duration);el.setAttribute('opacity',u>0&&u<1?Math.sin(Math.PI*u):0);};
  function draw(t){
   const first=ease((t-180)/760);flows.forEach((el,i)=>glow(el,t,isMixed?(i<2?360:1420):i<2?(isSquare?360:180):1910,isMixed?(i<2?800:1380):isSquare?(i<2?800:850):760));
   if(isMixed){
    const split=ease((t-180)/180),firstMove=ease((t-360)/800);
    const arrival=clamp((t-1420)/1380);
    // Integrated u(1-u)^4 velocity: leave rest, then brake strongly near K.
    // Both coordinates stay on their original arrow until the addition phase.
    const secondMove=1-(1-arrival)**5*(1+5*arrival);
    const combine=clamp((t-3100)/480)**2,morph=ease((t-3580)/360);
    seed.setAttribute('opacity',ease(t/120)*(1-split));
    const starts=[mix(a,[a[0]+11,a[1]],split),mix(a,[a[0],a[1]-11],split)];
    const intermediates=[h,v];
    dots.forEach((_,i)=>{
     const reached=mix(mix(starts[i],intermediates[i],firstMove),mixedStops[i],secondMove);
     const radius=(7-1.5*secondMove)*(1-morph);
     dot(i,mix(reached,additionCenter,combine),split*(1-morph),radius);
    });
    plus.setAttribute('opacity',ease((t-2480)/260)*(1-morph));
    const zero=zeros[0],scale=.08+.92*morph;
    zero.setAttribute('opacity',morph);
    zero.setAttribute('transform',`translate(${additionCenter[0]} ${additionCenter[1]}) scale(${scale}) translate(${-additionCenter[0]} ${-additionCenter[1]})`);
    result.style.opacity=String(ease((t-3860)/360));
   }else if(!isSquare){
    const gather=ease((t-1350)/820),fade=ease((t-2170)/400);
    dot(0,mix(mix(a,h,first),[sum[0]-30*(1-fade),sum[1]],gather),ease(t/180)*(1-fade));
    dot(1,mix(mix(a,v,first),[sum[0]+30*(1-fade),sum[1]],gather),ease(t/180)*(1-fade));
    // The result is typeset in C^{n+1}, outside every K-term.
    result.style.opacity=String(fade);zeros[0].setAttribute('opacity',0);
   }else{
    const split=ease((t-180)/180),firstMove=ease((t-360)/800);
    const hStart=[a[0]+11,a[1]],vStart=[a[0],a[1]-11];
    seed.setAttribute('opacity',ease(t/120)*(1-split));
    if(t<1650){
     dot(0,mix(mix(a,hStart,split),h,firstMove),split);
     dot(1,mix(mix(a,vStart,split),v,firstMove),split);
     dot(2,h,0);dot(3,v,0);
    }else{
     const fork=ease((t-1650)/260),secondMove=ease((t-1910)/850),cancel=ease((t-2960)/500);
     const fromHRight=mix(h,[h[0]+11,h[1]],fork),fromHUp=mix(h,[h[0],h[1]-11],fork);
     const fromVRight=mix(v,[v[0]+11,v[1]],fork),fromVUp=mix(v,[v[0],v[1]-11],fork);
     dot(0,mix(fromHRight,hh,secondMove),1-cancel,7*(1-cancel));
     dot(3,mix(fromVUp,vv,secondMove),fork*(1-cancel),7*(1-cancel));
     dot(2,mix(fromHUp,[m[0],m[1]+10*(1-cancel)],secondMove),fork*(1-cancel));
     dot(1,mix(fromVRight,[m[0]-10*(1-cancel),m[1]],secondMove),1-cancel);
    }
    const collapse=ease((t-2960)/500);
    zeros.forEach(z=>{const x=Number(z.getAttribute('x')),y=Number(z.getAttribute('y')),scale=.2+.8*collapse;z.setAttribute('opacity',collapse);z.setAttribute('transform',`translate(${x} ${y}) scale(${scale}) translate(${-x} ${-y})`);});
    result.style.opacity=String(ease((t-3460)/400));
   }
   for(const label of host.querySelectorAll('.term-label')){
    const x=parseFloat(label.style.left)+parseFloat(label.style.width)/2,y=parseFloat(label.style.top)+parseFloat(label.style.height)/2;
    const focus=dots.some(d=>Number(d.getAttribute('opacity'))>.05&&Math.abs(Number(d.getAttribute('cx'))-x)<34&&Math.abs(Number(d.getAttribute('cy'))-y)<19)||(isSquare||isMixed)&&zeros.some(z=>Number(z.getAttribute('opacity'))>.05&&Math.abs(Number(z.getAttribute('x'))-x)<34&&Math.abs(Number(z.getAttribute('y'))-y)<19);
    label.toggleAttribute('data-total-focus',focus);
   }
   layer.dataset.phase=isMixed?(t<360?'split':t<1160?'first-maps':t<1420?'intermediate':t<2180?'mixed-composites':t<2800?'braking':t<3100?'opposite-elements':t<3580?'addition':t<4220?'zero-morph':'complete'):isSquare?(t<360?'first-split':t<1160?'first-differential':t<1650?'first-image':t<1910?'second-split':t<2760?'second-differential':t<2960?'second-image':t<3860?'cancellation':'complete'):(t<940?'first-differential':t<1250?'summands':t<2120?'second-stage':t<2910?'combination':'complete');
  }
  const duration=isMixed?4450:isSquare?4100:3100;
  if(reduced()){draw(duration);running=false;return;}
  const start=performance.now();draw(0);const tick=now=>{if(run!==token)return;const elapsed=reduced()?duration:now-start;draw(elapsed);if(elapsed<duration)frame=requestAnimationFrame(tick);else running=false;};frame=requestAnimationFrame(tick);
 }
 return {play,clear,sync(effect,enabled){if(layer&&(!enabled||effect!==kind))clear();}};
}
