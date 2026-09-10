import {replaceMathContent} from './math-transitions.js?v=40';
import {visualMotion} from './visual-style.js?v=40';
// Z_r and B_r live in the filtered total complex, not in a single K-term.
// Regions encode subspace relations only; their areas never encode dimensions.
export function createFilteredView({viewport,board,math,language}){
 const R=String.raw,t=(zh,en)=>language()==='en'?en:zh;
 const host=document.createElement('div');host.id='filteredView';host.inert=true;host.setAttribute('aria-hidden','true');viewport.append(host);
 let state=null,active=false,key='',topic='Z';const steps={Z:0,B:0};
 const reduced=()=>matchMedia('(prefers-reduced-motion:reduce)').matches;
 const label=(x,y,tex,width=200,kind='')=>`<span class="filtered-label ${kind}" style="left:${x-width/2}px;top:${y-22}px;width:${width}px">${math(tex)}</span>`;
 const names={Z:[['逆像条件','Preimage condition'],['逐列条件','Column conditions'],['第一步','First step'],['随 r 变化','As r varies']],B:[['像与交集','Image and intersection'],['代表元条件','Representative condition'],['一定是闭元','Always a cocycle'],['随 r 变化','As r varies']]};
 function exposition(){
  const r=Math.max(1,state.r),n=state.n,p=state.p,q=n-p,i=steps[topic];
  const proof=topic==='Z'?[
   [R`Z_r^{p,q}:=\{a\in F^pC^n:Da\in F^{p+r}C^{n+1}\},\qquad n=p+q`,R`Z_r^{p,q}=\ker\big(F^pC^n\xrightarrow{D}C^{n+1}\xrightarrow{\pi}C^{n+1}/F^{p+r}C^{n+1}\big)`],
   [R`a=\sum_{i\ge p}a_i,\qquad a_i\in K^{i,n-i}`,R`(Da)_i=\delta_1a_{i-1}+\delta_2a_i`,R`a\in Z_r^{p,q}\iff\delta_1a_{i-1}+\delta_2a_i=0\quad(p\le i<p+r)`,R`a_i=0\quad(i<p)`],
   [R`a\in Z_1^{p,q}\iff\delta_2a_p=0`,R`a\in Z_2^{p,q}\iff\begin{cases}\delta_2a_p=0,\\\delta_1a_p+\delta_2a_{p+1}=0.\end{cases}`],
   [R`F^{p+r+1}C^{n+1}\subseteq F^{p+r}C^{n+1}`,R`Z_{r+1}^{p,q}\subseteq Z_r^{p,q}`,R`p+r>n+1\ \Longrightarrow\ Z_r^{p,q}=F^pC^n\cap\ker D`]
  ]:[
   [R`B_r^{p,q}:=F^pC^n\cap D(F^{p-r}C^{n-1}),\qquad n=p+q`,R`x\in B_r^{p,q}\iff\exists b\in F^{p-r}C^{n-1}:x=Db\in F^pC^n`],
   [R`b=\sum_{i\ge p-r}b_i,\qquad b_i\in K^{i,n-1-i}`,R`(Db)_i=\delta_1b_{i-1}+\delta_2b_i`,R`Db\in F^pC^n\iff\delta_1b_{i-1}+\delta_2b_i=0\quad(i<p)`],
   [R`x=Db\ \Longrightarrow\ Dx=D^2b=0`,R`B_r^{p,q}\subseteq F^pC^n\cap\ker D\subseteq Z_s^{p,q}\quad(s\ge0)`],
   [R`F^{p-r}C^{n-1}\subseteq F^{p-r-1}C^{n-1}`,R`B_r^{p,q}\subseteq B_{r+1}^{p,q}`,R`r\ge p\ \Longrightarrow\ B_r^{p,q}=F^pC^n\cap D(C^{n-1})`]
  ];
  const note=topic==='Z'?[
   t('蓝色是像必须落入的滤过层；金色 Zᵣ 是满足此条件的全部原像，不是整个 FᵖCⁿ。','The blue region is the required filtration of the image. The gold Zᵣ consists of all preimages satisfying it, not all of FᵖCⁿ.'),
   t('需要检查各列分量之和的抵消。Zᵣ 通常不能表示为若干 K 小块的直和。','The sums of components must cancel in the excluded columns. In general Zᵣ is not a direct sum of selected K-terms.'),
   t('r=1 只检查首列；r=2 还要检查下一列。总次数 n 之外的分量为零。','For r=1 only the first column is tested; r=2 also tests the next. Components outside total degree n are zero.'),
   t('r 增大时像的条件更强，Zᵣ 缩小；目标滤过为零时，就要求 Da=0。','As r grows, the image condition becomes stronger and Zᵣ decreases. When the target filtration is zero, Da must be zero.')
  ]:[
   t('D 的像是蓝色区域；还需落入 FᵖCⁿ，交集才是 Bᵣ。没有从全部 Fᵖ⁻ʳCⁿ⁻¹ 到 Bᵣ 的无条件映射。','The blue region is the image of D. Its intersection with FᵖCⁿ is Bᵣ. The whole source does not map into Bᵣ without the filtration condition.'),
   t('b 可以从 p−r 列开始，但 Db 的所有 p 列之前的分量必须抵消。','The representative b may start in column p−r, but all components of Db before column p must cancel.'),
   t('这是总复形中的边界，因此由 D²=0 自动得到闭性。','These are boundaries in the total complex; D²=0 makes them cocycles.'),
   t('r 增大时允许更多来源，所以 Bᵣ 增大。注意 Eᵣ 的分母使用 Bᵣ₋₁。','As r grows, more source columns are allowed and Bᵣ increases. The denominator of Eᵣ uses Bᵣ₋₁.')
  ];
  board.dataset.currentProofTopic=topic;board.dataset.currentProofStep=String(i);
  replaceMathContent(board,`<nav class="proof-steps" aria-label="${t('证明关键步骤','Key proof steps')}">${names[topic].map((name,j)=>`<button data-filter-step="${j}" aria-pressed="${i===j}">${j+1}. ${t(...name)}</button>`).join('')}</nav><div class="operation-content">${proof[i].map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}</div><p class="operation-note">${note[i]}</p><p class="filtered-example">${math(R`n=${n},\quad p=${p},\quad q=${q},\quad r=${r}`)}</p>`);
 }
 function draw(){
  const {n,p}=state,r=Math.max(1,state.r),q=n-p,Z=`Z_{${r}}^{${p},${q}}`,B=`B_{${r}}^{${p},${q}}`;
  const F=`F^{${p}}C^{${n}}`,target=`F^{${p+r}}C^{${n+1}}`,source=`F^{${p-r}}C^{${n-1}}`,image=R`D(${source})`;
  let shapes='',labels='';
  if(topic==='Z'){
   shapes=`<ellipse class="filtered-ambient" cx="207" cy="255" rx="150" ry="155"/><ellipse class="filtered-ambient" cx="637" cy="255" rx="150" ry="155"/><ellipse class="filtered-region gold" data-filter-region="Z" cx="235" cy="290" rx="92" ry="87"/><ellipse class="filtered-region blue" data-filter-region="target" cx="610" cy="290" rx="92" ry="87"/><path class="filtered-map" d="M360,180 C410,150 430,150 479,180" marker-end="url(#filtered-tip)"/><path class="filtered-map strong" data-filter-map="restriction" d="M331,290 H506" marker-end="url(#filtered-tip)"/>`;
   labels=label(202,148,F+(p>n?'=0':''),230)+label(639,148,`C^{${n+1}}`,180)+label(235,290,Z+(p>n?'=0':''),180,'gold')+label(610,290,target+(p+r>n+1?'=0':''),200,'blue')+label(420,145,'D',70)+label(420,258,R`D|_{${Z}}`,140)+label(235,337,R`a`,50,'muted')+label(610,337,R`Da`,80,'muted');
   if(p+r>n+1){
    shapes=shapes.replace(/<ellipse class="filtered-region blue"[^>]+\/>/,'<circle class="filtered-zero blue" cx="610" cy="290" r="4"/>').replace('M331,290 H506','M331,290 H596');
    labels=label(202,148,F+(p>n?'=0':''),230)+label(639,148,`C^{${n+1}}`,180)+label(235,290,Z+(p>n?'=0':''),180,'gold')+label(610,244,target+'=0',220,'blue')+label(420,145,'D',70)+label(420,258,R`D|_{${Z}}`,140)+label(235,337,'a',50,'muted')+label(610,337,'Da=0',110,'muted');
   }
   if(p>n){
    shapes='<ellipse class="filtered-ambient" cx="637" cy="255" rx="150" ry="155"/><circle class="filtered-zero gold" cx="235" cy="290" r="4"/><circle class="filtered-zero blue" cx="610" cy="290" r="4"/><path class="filtered-map strong" d="M247,290 H596" marker-end="url(#filtered-tip)"/>';
    labels=label(235,244,F+'=0',220)+label(235,337,Z+'=0',220,'gold')+label(639,148,`C^{${n+1}}`,180)+label(610,244,target+'=0',220,'blue')+label(420,258,'D',70);
   }
  }else{
   const zeroSource=n===0||p-r>n-1,zeroResult=zeroSource||p>n;
   shapes=`<defs><clipPath id="filtered-intersection"><ellipse cx="535" cy="277" rx="125" ry="117"/></clipPath></defs><ellipse class="filtered-ambient" cx="142" cy="270" rx="116" ry="133"/><ellipse class="filtered-ambient" cx="601" cy="255" rx="219" ry="175"/><ellipse class="filtered-region blue" data-filter-region="image" cx="535" cy="277" rx="125" ry="117"/><ellipse class="filtered-region" data-filter-region="filtration" cx="666" cy="277" rx="125" ry="117"/><ellipse class="filtered-intersection gold" data-filter-region="B" cx="666" cy="277" rx="125" ry="117" clip-path="url(#filtered-intersection)"/><path class="filtered-map strong" data-filter-map="image" d="M264,270 H400" marker-end="url(#filtered-tip)"/>`;
   labels=label(142,258,source+(zeroSource?'=0':''),235)+label(603,119,`C^{${n}}`,160)+label(503,198,image+(zeroSource?'=0':''),235,'blue small')+label(699,230,F+(p>n?'=0':''),185,'small')+label(600,310,B+(zeroResult?'=0':''),130,'gold')+label(329,240,'D',70);
   if(p===0&&!zeroResult){
    shapes='<ellipse class="filtered-ambient" cx="142" cy="270" rx="116" ry="133"/><ellipse class="filtered-ambient" cx="601" cy="255" rx="219" ry="175"/><ellipse class="filtered-region gold" data-filter-region="B" cx="580" cy="282" rx="144" ry="113"/><path class="filtered-map strong" d="M264,270 H422" marker-end="url(#filtered-tip)"/>';
    labels=label(142,258,source,235)+label(603,119,F+`=C^{${n}}`,300)+label(580,282,B+'='+image,285,'gold small')+label(329,240,'D',70);
   }else if(zeroResult){
    shapes=(zeroSource?'<circle class="filtered-zero" cx="142" cy="270" r="4"/>':'<ellipse class="filtered-ambient" cx="142" cy="270" rx="116" ry="133"/>')+'<ellipse class="filtered-ambient" cx="601" cy="255" rx="219" ry="175"/>';
    if(zeroSource){
     shapes+=(p>n?'':'<ellipse class="filtered-region" cx="666" cy="277" rx="125" ry="117"/>')+'<circle class="filtered-zero gold" data-filter-region="B" cx="615" cy="277" r="4"/><path class="filtered-map strong" d="M155,270 H600" marker-end="url(#filtered-tip)"/>';
     labels=label(142,220,source+'=0',235)+label(603,119,`C^{${n}}`,160)+label(665,220,F+(p>n?'=0':''),210)+label(610,335,B+'=0',180,'gold')+label(415,190,image+'=0',220,'blue small')+label(340,242,'D',70);
     if(p===0){shapes=shapes.replace(/<ellipse class="filtered-region"[^>]+\/>/,'');labels=label(142,220,source+'=0',235)+label(603,119,F+`=C^{${n}}`,300)+label(610,335,B+'=0',180,'gold')+label(610,226,image+'=0',240,'blue small')+label(340,242,'D',70);}
    }else{
     shapes+='<ellipse class="filtered-region blue" cx="535" cy="277" rx="125" ry="117"/><circle class="filtered-zero gold" data-filter-region="B" cx="560" cy="305" r="4"/><path class="filtered-map strong" d="M264,270 H400" marker-end="url(#filtered-tip)"/>';
     labels=label(142,258,source,235)+label(603,119,`C^{${n}}`,160)+label(535,212,image,235,'blue small')+label(560,348,B+'='+F+'=0',330,'gold small')+label(329,240,'D',70);
    }
   }
  }
  const scene=document.createElement('div');scene.className='filtered-scene';scene.dataset.filterTopic=topic;
  scene.innerHTML=`<svg viewBox="0 0 840 525" aria-hidden="true"><defs><marker id="filtered-tip" markerUnits="userSpaceOnUse" markerWidth="9" markerHeight="9" refX="7" refY="4.5" orient="auto"><path d="M1.5,1.5 L7,4.5 L1.5,7.5" fill="none" stroke="#a7d3ca" stroke-width="1.5"/></marker></defs>${shapes}</svg>${labels}<p class="filtered-caption">${t('子空间示意 · 区域大小不表示维数','Subspace diagram · region sizes do not encode dimensions')}</p>`;
  for(const old of [...host.children]){
   const opacity=getComputedStyle(old).opacity;old.getAnimations().forEach(a=>a.cancel());old.style.opacity=opacity;
   if(reduced())old.remove();else{const fade=old.animate([{opacity},{opacity:0}],{duration:visualMotion().exit,fill:'forwards',easing:visualMotion().easing});fade.finished.then(()=>old.remove(),()=>{});}
  }
  host.append(scene);
  if(!reduced())scene.animate([{opacity:0},{opacity:1}],{duration:visualMotion().emphasis,easing:visualMotion().easing});
 }
 function fit(){const bounds=viewport.getBoundingClientRect(),width=Math.min(bounds.width,bounds.height*840/525);host.style.width=width+'px';host.style.height=width*525/840+'px';host.style.setProperty('--filtered-scale',String(width/840));}
 board.addEventListener('click',e=>{const button=e.target.closest('[data-filter-step]');if(!active||!button)return;e.stopPropagation();steps[topic]=Number(button.dataset.filterStep);exposition();});
 new ResizeObserver(fit).observe(viewport);
 return {sync(s){
  state=s;active=!s.cover&&s.module==='learn'&&s.step===5&&(s.annotationStep===1||s.annotationStep===2);
  viewport.classList.toggle('has-filtered-view',active);host.classList.toggle('is-active',active);host.inert=!active;host.setAttribute('aria-hidden',String(!active));
  if(!active){key='';return;}
  topic=s.annotationStep===1?'Z':'B';const next=[topic,s.n,s.p,s.r,language()].join(':');
  if(next!==key){key=next;draw();}fit();exposition();
 }};
}
