// The same affine page geometry as page-evolution.js. These are schematic
// vector-space terms, never a claimed map from all of E_r to E_{r+1}.
export function createConvergencePages({math,language}){
 const R=String.raw,t=(zh,en)=>language()==='en'?en:zh;
 let scene=null,baseline='',kind='',frame=0,resolveRun=null,serial=0,busy=false;
 const clamp=x=>Math.max(0,Math.min(1,x)),ease=x=>{x=clamp(x);return x*x*(3-2*x);};
 const label=(x,y,tex,cls='',width=160)=>`<span class="cp-label ${cls}" style="left:${x-width/2}px;top:${y-18}px;width:${width}px">${math(tex)}</span>`;
 const xy=(p,q,i)=>[65+210*i+35*p,310+26*p-54*q];
 function stop(){serial++;cancelAnimationFrame(frame);frame=0;busy=false;resolveRun?.();resolveRun=null;if(scene&&baseline){scene.innerHTML=baseline;scene.dataset.stage='-1';}window.spectralConvergencePages={kind,stage:-1,playing:false};}
 function build(type){
  stop();kind=type;scene=document.createElement('div');scene.className='abutment-scene convergence-pages';scene.dataset.kind=kind;
  let pages='';
  for(let i=0;i<3;i++){
   let svg='',labels='';const r=kind==='convergence'?[2,3,5][i]:i+2;
   for(let k=0;k<=3;k++){
    const a=xy(k,0,i),b=xy(k,3,i),c=xy(0,k,i),d=xy(3,k,i);
    svg+=`<path class="cp-grid" d="M${a} L${b} M${c} L${d}"/>`;
   }
   for(let p=0;p<=3;p++)for(let q=0;q<=3;q++){
    const [x,y]=xy(p,q,i);
    svg+=`<circle class="cp-dot" data-p="${p}" data-q="${q}" cx="${x}" cy="${y}" r="3"/>`;
    labels+=label(x,y-11,`E_{${r}}^{${p},${q}}`,'cp-term',74).replace('class="cp-label cp-term"',`class="cp-label cp-term" data-p="${p}" data-q="${q}" data-r="${r}"`);
   }
   labels+=label(118+210*i,68,`E_${r}`,'cp-page-title',180);
   // Incoming/outgoing differentials are indicated by their zero endpoints
   // rather than by animating a nonzero element to an arbitrary next page.
   pages+=`<div class="cp-page" data-slice="${i}"><svg viewBox="0 0 840 525">${svg}</svg>${labels}</div>`;
  }
  scene.innerHTML=`<style>
   .convergence-pages .cp-page{position:absolute;inset:0;will-change:transform,opacity}
   .convergence-pages svg{position:absolute;inset:0;width:840px;height:525px}
   .cp-grid{stroke:var(--muted);stroke-width:.65;opacity:.19;fill:none}
   .cp-dot{fill:var(--gold);opacity:.6;transition:opacity .6s,fill .6s}
   .cp-label{position:absolute;display:flex;align-items:center;justify-content:center;height:36px;color:var(--ink);white-space:nowrap;font-size:15px;transition:color .6s,opacity .6s}
   .cp-term{font-size:12px;opacity:.5}.cp-term.is-live{opacity:1;color:var(--gold)}.cp-term.is-zero{opacity:.23}
   .cp-page-title{font-size:23px;color:var(--gold)}
   .cp-caption{position:absolute;top:14px;left:20px;width:800px;text-align:center;color:var(--muted);font-size:17px}
   .cp-result{position:absolute;left:15px;top:411px;width:810px;text-align:center;color:var(--gold);font-size:17px;line-height:1.6}
   .cp-result .katex{font-size:1em}.cp-proof-line{position:absolute;top:111px;left:10px;width:820px;text-align:center;font-size:17px;color:var(--ink)}
   </style><div class="cp-caption"></div>${pages}<div class="cp-grade-boxes" style="position:absolute;inset:0;opacity:0">${[0,1,2,3].map(p=>`<div style="position:absolute;left:${45+195*p}px;top:320px;width:150px;height:54px;border:1px solid var(--gold);border-radius:8px"></div>`).join('')}</div><div class="cp-proof-line"></div><div class="cp-result"></div>`;
  stage(-1);baseline=scene.innerHTML;return scene;
 }
 function setText(selector,tex){const el=scene.querySelector(selector);el.innerHTML=math(tex);if(!matchMedia('(prefers-reduced-motion:reduce)').matches)el.animate([{opacity:0},{opacity:1}],{duration:450});}
 function stage(s){
  if(!scene)return;scene.dataset.stage=String(s);
  const caption=scene.querySelector('.cp-caption'),result=scene.querySelector('.cp-result');
  if(kind==='degeneration'){
   caption.innerHTML=math(R`r_0=2,\qquad d_s^{p,q}=0\quad(\forall s\ge2,\ \forall p,q)`);
   if(s>=1)setText('.cp-proof-line',R`E_{s+1}^{p,q}\cong\ker d_s^{p,q}/\operatorname{im}d_s^{p-s,q+s-1}=E_s^{p,q}/0`);
   if(s>=2){scene.querySelector('[data-slice="0"] .cp-page-title').innerHTML=math(R`E_2\cong E_\infty`);result.innerHTML=math(R`E_2^{p,q}\cong E_\infty^{p,q}`);}
  }else if(kind==='convergence'){
   caption.textContent=t('固定总次数 n = 3；图示有限窗口','Fix total degree n = 3; a finite window is shown');
   if(s>=1){
    for(const el of scene.querySelectorAll('.cp-term,.cp-dot')){
     const diagonal=Number(el.dataset.p)+Number(el.dataset.q)===3;
     el.style.opacity=diagonal?'1':'.13';el.classList.toggle('is-live',diagonal);
    }
    setText('.cp-proof-line',R`s\ge5>\max\{p,q+1\}\quad(p+q=3):\quad d_s^{p,q}=d_s^{p-s,q+s-1}=0`);
   }
   if(s>=2){
    scene.querySelector('[data-slice="2"] .cp-page-title').innerHTML=math(R`E_5`);
    for(const el of scene.querySelectorAll('[data-slice="2"] .cp-term'))if(+el.dataset.p+ +el.dataset.q===3){delete el.dataset.graded;el.innerHTML=math(`E_\\infty^{${el.dataset.p},${el.dataset.q}}`);}
    result.innerHTML=math(R`[a]_\infty\longmapsto[a]_H+F^{p+1}H^3,\qquad E_\infty^{p,3-p}\cong F^pH^3/F^{p+1}H^3`);
   }
   if(s>=3){
    result.innerHTML=math(R`F^pH^3=\operatorname{im}H^3(\iota_p),\qquad H^3=F^0H^3\supseteq\cdots\supseteq F^4H^3=0`);
    setText('.cp-proof-line',R`E_\infty^{p,3-p}\cong\frac{F^pC^3\cap\ker D}{(F^{p+1}C^3\cap\ker D)+(F^pC^3\cap\operatorname{im}D)}\cong\operatorname{Gr}_F^pH^3`);
   }
  }else{
   const column=s<4;caption.innerHTML=math(column?R`r_0=2:\quad E_2^{p,q}=0\ (p>0)` :R`r_0=2:\quad E_2^{p,q}=0\ (q>0)`);
   for(const el of scene.querySelectorAll('.cp-term')){
    const alive=column?+el.dataset.p===0:+el.dataset.q===0;
    el.classList.toggle('is-live',alive);el.classList.toggle('is-zero',!alive&&s>=0);
    const tex=!alive&&s>=0?'0':`E_${el.dataset.r}^{${el.dataset.p},${el.dataset.q}}`;if(el.dataset.tex!==tex){el.dataset.tex=tex;el.innerHTML=math(tex);if(!matchMedia('(prefers-reduced-motion:reduce)').matches)el.animate([{opacity:0},{opacity:alive?1:.23}],{duration:650});}
   }
   if(s===-1){result.innerHTML='';return;}
   if(s===0||s===4)setText('.cp-proof-line',column?R`0\xrightarrow{d_s^{-s,n+s-1}}E_s^{0,n}\xrightarrow{d_s^{0,n}}0\qquad(s\ge2)`:R`0\xrightarrow{d_s^{n-s,s-1}}E_s^{n,0}\xrightarrow{d_s^{n,0}}0\qquad(s\ge2)`);
   if(s===1||s===5)result.innerHTML=math(column?R`E_2^{0,n}\cong E_3^{0,n}\cong\cdots\cong E_\infty^{0,n}`:R`E_2^{n,0}\cong E_3^{n,0}\cong\cdots\cong E_\infty^{n,0}`);
   if(s===2||s===6)result.innerHTML=math(column?R`F^pH^n/F^{p+1}H^n\cong E_\infty^{p,n-p}=0\quad(1\le p\le n)`:R`F^pH^n/F^{p+1}H^n\cong E_\infty^{p,n-p}=0\quad(0\le p<n)`);
   if(s===3||s===7){
    setText('.cp-proof-line',column?R`F^1H^n=\cdots=F^{n+1}H^n=0`:R`H^n=F^0H^n=\cdots=F^nH^n,\quad F^{n+1}H^n=0`);
    result.innerHTML=math(column?R`H^n\cong F^0H^n/F^1H^n\cong E_\infty^{0,n}\cong E_2^{0,n}`:R`E_2^{n,0}\cong E_\infty^{n,0}\cong F^nH^n/F^{n+1}H^n\cong H^n`);
   }
  }
 }
 function play(){
  if(!scene)return Promise.resolve();stop();busy=true;const id=serial,start=performance.now(),duration=kind==='extreme'?24000:kind==='convergence'?16000:7500;let previous=-2;
  return new Promise(resolve=>{resolveRun=resolve;const tick=now=>{
   if(id!==serial)return;const elapsed=matchMedia('(prefers-reduced-motion:reduce)').matches?duration:Math.min(duration,now-start);
   const s=kind==='extreme'?Math.min(7,Math.floor(elapsed/3000)):kind==='convergence'?Math.min(3,Math.floor(elapsed/4000)):elapsed<2500?0:elapsed<5300?1:2;
   if(s!==previous){stage(s);previous=s;}
   for(const page of scene.querySelectorAll('.cp-page')){
    const i=+page.dataset.slice;let collapse=0;
    if(kind==='degeneration')collapse=ease((elapsed-3200)/2100);
    if(kind==='extreme')collapse=ease(((elapsed===duration?11999:elapsed%12000)-4000)/1700);
    page.style.transform=`translateX(${-210*i*collapse}px)`;page.style.opacity=String(i?1-collapse:1);
    if(kind==='convergence'&&i<2)page.style.opacity=String(1-.88*ease((elapsed-12000)/1100));
   }
   if(kind==='convergence'){
    const transfer=ease((elapsed-12400)/1500);scene.querySelector('.cp-grade-boxes').style.opacity=String(transfer);
    const last=scene.querySelector('[data-slice="2"]');
    last.querySelector('svg').style.opacity=String(1-.88*transfer);
    for(const el of last.querySelectorAll('.cp-term')){
     const p=+el.dataset.p,q=+el.dataset.q;if(p+q!==3)continue;
     const [x,y]=xy(p,q,2);el.style.transform=`translate(${(120+195*p-x)*transfer}px,${(347-(y-11))*transfer}px)`;
     el.style.fontSize=`${12+6*transfer}px`;
     if(transfer===1&&!el.dataset.graded){el.dataset.graded='true';el.innerHTML=math(`\\operatorname{Gr}_F^{${p}}H^3`);}
    }
   }
   window.spectralConvergencePages={kind,stage:s,playing:elapsed<duration};
   if(elapsed<duration)frame=requestAnimationFrame(tick);else{busy=false;frame=0;resolveRun=null;resolve();}
  };tick(start);});
 }
 return {build,play,stop,isPlaying:()=>busy};
}
