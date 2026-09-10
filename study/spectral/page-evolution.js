import {createDifferentialProof} from './differential-proof.js?v=47';
// The existing two-dimensional diagram is the physical E0 plane.
// Its affine projection changes only the view. Further pages are cohomology objects.
export function createPageEvolution({origin,viewport,diagram,controls,board,math,language}){
 const R=String.raw,t=(zh,en)=>language()==='en'?en:zh,reduced=matchMedia('(prefers-reduced-motion:reduce)');
 const proof=createDifferentialProof({board,math,language});
 const overlay=document.createElement('div');overlay.id='pageEvolution';overlay.hidden=true;viewport.append(overlay);
 const toolbar=document.createElement('nav');toolbar.id='evolutionControls';toolbar.hidden=true;controls.prepend(toolbar);
 let context=null,engaged=false,tilted=false,generated=0,current=0,start=0,semanticKey='',token=0,busy=false,construction=null,point={p:1,q:2},transformAnimation=null,scale=1,projectionKey='',transformTarget='',layerAnimations=[];
 const zeroPageOnly=()=>context?.module==='learn'&&context.step===3;
 const compact=()=>matchMedia('(max-width:780px)').matches;
 const geometry=()=>compact()?{x:110,y:360,dp:55,dq:64,yp:24,dr:400,count:2}:{x:55,y:345,dp:35,dq:54,yp:26,dr:210,count:4};
 const pos=(p,q,r)=>{const g=geometry();return [g.x+g.dp*p+g.dr*(r-start),g.y+g.yp*p-g.dq*q];};
 const color=r=>['var(--blue)','var(--teal)','var(--gold)','#d9b7ec'][r%4];
 // Hand off the whole source layer only when its projection has reached the
 // destination. Crossfading earlier would draw E0 in two different positions.
 function settleProjection(){
  const ready=engaged&&tilted;
  diagram.classList.toggle('evolution-settled',ready);
  overlay.classList.toggle('is-tilted',ready);
  diagram.inert=ready;
 }
 function fit(animate=false){
  const bounds=viewport.getBoundingClientRect(),width=Math.min(bounds.width,bounds.height*840/525);scale=width/840;overlay.style.width=width+'px';overlay.style.height=width*525/840+'px';overlay.style.setProperty('--evolution-scale',String(scale));
  const g=geometry(),a=g.dp/125,b=g.yp/125,d=g.dq/75,e=g.x-start*g.dr-a*origin.x,f=g.y-b*origin.x-d*origin.y;
  const target=tilted?`matrix(${a},${b},0,${d},${e*scale},${f*scale})`:'matrix(1,0,0,1,0,0)';
  if(transformTarget!==target){
   const previous=getComputedStyle(diagram).transform,wasSettled=diagram.classList.contains('evolution-settled');
   transformAnimation?.cancel();transformAnimation=null;transformTarget=target;
   diagram.classList.remove('evolution-settled');overlay.classList.remove('is-tilted');diagram.inert=false;
   diagram.style.transform=target;
   if(animate&&!reduced.matches){
    const motion=diagram.animate([{transform:previous},{transform:target}],{duration:900,delay:!tilted&&wasSettled?160:0,fill:'backwards',easing:'cubic-bezier(.22,.68,.18,1)'});
    transformAnimation=motion;
    motion.finished.then(()=>{if(transformAnimation===motion)settleProjection();},()=>{});
   }else settleProjection();
  }else if(!transformAnimation||transformAnimation.playState==='finished')settleProjection();
  diagram.classList.toggle('evolution-tilted',tilted);overlay.dataset.tilted=String(tilted);
 }
 // Formula labels share the SVG's 840-by-525 coordinate space. Keeping them
 // in a scaled HTML layer uses the same KaTeX typography as the source grid.
 function mathLabel(x,y,tex,kind,{width=80,height=32,align='center'}={}){
  const left=align==='right'?x-width:align==='left'?x:x-width/2;
  return `<span class="evolution-math-label ${kind}" data-tex="${tex}" style="left:${left}px;top:${y-height/2}px;width:${width}px;height:${height}px;justify-content:${align==='right'?'flex-end':align==='left'?'flex-start':'center'}">${math(tex)}</span>`;
 }
 function pageMarkup(r){
  const g=geometry(),c=color(r),corners=[[0,0],[4,0],[4,4],[0,4]].map(([p,q])=>pos(p,q,r).join(',')).join(' '),origin=pos(0,0,r);
  let svg=`<g class="evolution-page ${r===current?'is-current':''}" data-r="${r}" style="--evolution-color:${c}"><polygon class="evolution-sheet" points="${corners}"/>`;
  let labels=`<div class="evolution-label-page ${r===current?'is-current':''}" data-label-r="${r}" aria-hidden="true" style="--evolution-color:${c}">`;
  for(let i=0;i<=4;i++){const a=pos(i,0,r),b=pos(i,4,r),c=pos(0,i,r),d=pos(4,i,r);svg+=`<path class="evolution-grid" d="M${a} L${b} M${c} L${d}"/>`;}
  for(let p=0;p<=4;p++)for(let q=0;q<=4;q++){const [x,y]=pos(p,q,r),selected=p===point.p&&q===point.q;svg+=`<g class="evolution-point ${selected?'is-selected':''}" role="button" tabindex="${selected?'0':'-1'}" data-page="${r}" data-p="${p}" data-q="${q}" aria-label="E_${r}^{${p},${q}}"><circle class="evolution-hit" cx="${x}" cy="${y}" r="10"/><circle class="evolution-dot" cx="${x}" cy="${y}" r="${selected?5:2.8}"/></g>`;}
  const [p,q]=[point.p,point.q],tp=p+r,tq=q-r+1,source=pos(p,q,r);
  if(tp<=4&&tq>=0&&tq<=4){
   const target=pos(tp,tq,r),dx=target[0]-source[0],dy=target[1]-source[1],len=Math.hypot(dx,dy);
   svg+=`<path class="evolution-differential" data-source="${p},${q},${r}" data-target="${tp},${tq},${r}" d="M${source[0]+dx*9/len},${source[1]+dy*9/len} L${target[0]-dx*9/len},${target[1]-dy*9/len}" marker-end="url(#evolution-tip-${r%4})"/>`;
   labels+=mathLabel((source[0]+target[0])/2+8,(source[1]+target[1])/2-12,`d_{${r}}`,'evolution-d-label',{width:40,height:28,align:'left'});
  }
  if(construction&&construction.r===r){
   const map=(fp,fq,tp,tq,cls)=>{
    if([fp,fq,tp,tq].some(v=>v<0||v>4))return;
    const a=pos(fp,fq,r),b=pos(tp,tq,r),dx=b[0]-a[0],dy=b[1]-a[1],len=Math.hypot(dx,dy);
    svg+=`<path class="evolution-differential co-context-map ${cls}" data-source="${fp},${fq},${r}" data-target="${tp},${tq},${r}" d="M${a[0]+dx*9/len},${a[1]+dy*9/len} L${b[0]-dx*9/len},${b[1]-dy*9/len}" marker-end="url(#evolution-tip-${r%4})"/>`;
    labels+=mathLabel((a[0]+b[0])/2+16,(a[1]+b[1])/2,`d_{${r}}`,'evolution-d-label',{width:35,height:26});
   };
   if(r===0){for(let j=0;j<4;j++)if(j!==q)map(p,j,p,j+1,j===q-1?'co-incoming':'');}
   else map(p-r,q+r-1,p,q,'co-incoming');
  }
  labels+=mathLabel(source[0]+(source[0]<70?12:-12),source[1]-2,`E_{${r}}^{${p},${q}}`,'evolution-point-label',{width:86,height:36,align:source[0]<70?'left':'right'});
  svg+=`<g role="button" tabindex="0" data-page="${r}" class="evolution-page-title" aria-label="E_${r}"><rect x="${origin[0]-12}" y="37" width="${g.dp*4+24}" height="39" rx="8"/></g></g>`;
  labels+=mathLabel(origin[0]+g.dp*2,56.5,`E_{${r}}`,'evolution-page-title-label',{width:g.dp*4+24,height:39});
  labels+=mathLabel(origin[0],g.y+22,String(r),'evolution-r-tick',{width:40,height:24});
  return {svg,labels:labels+'</div>'};
 }
 function drawPages(newPage=null){
  const g=geometry(),visibleMax=zeroPageOnly()?0:generated;start=Math.max(0,Math.min(start,Math.max(0,visibleMax-g.count+1)));
  if(current<start)start=current;else if(current>=start+g.count)start=current-g.count+1;
  const key=[start,Math.min(visibleMax,start+g.count-1),current,point.p,point.q,language(),compact(),construction?.r].join(':');
  if(key!==projectionKey){
   let out='<svg viewBox="0 0 840 525" role="group" aria-label="'+t('由二维 E0 连续展开的谱序列各页','Spectral-sequence pages unfolding from the original two-dimensional E0')+'"><defs>',labels='',pages='';
   for(let i=0;i<4;i++)out+=`<marker id="evolution-tip-${i}" markerUnits="userSpaceOnUse" markerWidth="9" markerHeight="9" refX="7" refY="4.5" orient="auto"><path d="M1.5,1.5 L7,4.5 L1.5,7.5" fill="none" stroke="${color(i)}" stroke-width="1.3"/></marker>`;
   out+=`</defs><path class="evolution-r-axis" d="M28,${g.y} H817" marker-end="url(#evolution-tip-0)"/>`;
   labels+=mathLabel(815,g.y-17,'r','evolution-axis-label',{width:24,height:24});
   if(start>0)labels+=mathLabel(10,g.y-13,R`\cdots`,'evolution-axis-label',{width:22,height:24});
   for(let r=start;r<=Math.min(visibleMax,start+g.count-1);r++){const page=pageMarkup(r);pages+=`<div class="evolution-page-layer ${construction?.r===r?'is-source':''}" data-layer-r="${r}"><svg viewBox="0 0 840 525">${page.svg}</svg>${page.labels}</div>`;}
   const pAxis=pos(4.6,0,start),qAxis=pos(0,4.5,start),o=pos(0,0,start);
   out+=`<path class="evolution-r-axis" d="M${o} L${pAxis} M${o} L${qAxis}"/></svg>`;
   labels+=mathLabel(pAxis[0]+8,pAxis[1]-5,'p','evolution-axis-label',{width:24,height:24})+mathLabel(qAxis[0]-18,qAxis[1]-5,'q','evolution-axis-label',{width:24,height:24});
   overlay.innerHTML=`<div class="evolution-scene">${out}${pages}<div class="evolution-axis-labels" aria-hidden="true">${labels}</div></div>`;projectionKey=key;
   if(newPage!==null&&!reduced.matches){
    // The new page remains a distinct object. Columns pulse on the source;
    // cohomology terms appear at the same (p,q) on the new r-plane.
    // No arrow or vector trajectory from all of E_r to E_{r+1} is implied.
    const layer=overlay.querySelector(`[data-layer-r="${newPage}"]`),sourcePage=newPage-1;
    if(layer){
     layerAnimations.push(layer.animate([{opacity:0,transform:`translateX(${-g.dr*.32}px)`},{opacity:1,transform:'translateX(0)'}],{duration:1000,easing:'cubic-bezier(.22,.68,.18,1)'}));
     for(const node of layer.querySelectorAll('.evolution-point')){
      const p=Number(node.dataset.p),q=Number(node.dataset.q),delay=380+150*(sourcePage===1?q:p)+55*(sourcePage===1?p:q);
      layerAnimations.push(node.animate([{opacity:0},{opacity:1}],{duration:520,delay,fill:'backwards'}));
      const circle=node.querySelector('.evolution-dot'),cx=circle.getAttribute('cx'),cy=circle.getAttribute('cy');
      circle.style.transformOrigin=`${cx}px ${cy}px`;
      layerAnimations.push(circle.animate([{transform:'scale(.3)'},{transform:'scale(1.6)',offset:.65},{transform:'scale(1)'}],{duration:620,delay,fill:'backwards',easing:'ease-out'}));
     }
     for(const el of layer.querySelectorAll('.evolution-differential,.evolution-d-label'))layerAnimations.push(el.animate([{opacity:0},{opacity:1}],{duration:450,delay:1300,fill:'backwards'}));
     for(const el of layer.querySelectorAll('.evolution-point-label'))layerAnimations.push(el.animate([{opacity:0},{opacity:1}],{duration:450,delay:650,fill:'backwards'}));
    }
    for(const el of overlay.querySelectorAll(`[data-r="${sourcePage}"] .evolution-dot`)){
     const term=el.parentElement,group=sourcePage===1?Number(term.dataset.q):Number(term.dataset.p);
     const rest=getComputedStyle(el);layerAnimations.push(el.animate([{opacity:rest.opacity,fill:rest.fill},{opacity:1,fill:'var(--gold)',offset:.45},{opacity:rest.opacity,fill:rest.fill}],{duration:700,delay:150*group,easing:'ease-in-out'}));
    }
   }
  }
  fit();window.spectralEvolution={engaged,tilted,generated,current,start,busy,point:{...point},construction:construction?{...construction}:null};
 }
 function exposition(){proof.render({state:context,current,construction,point});}

 function paintControls(){
  toolbar.hidden=!engaged;
  toolbar.innerHTML=`<div class="evolution-view-controls"><button data-evolve="flat" aria-pressed="${!tilted}">${t('二维','2D')} ${math('E_0')}</button><button data-evolve="tilt" aria-pressed="${tilted}">${t('各页','Pages')}</button><select id="evolutionPage" aria-label="${t('查看已生成的页','Inspect a generated page')}" ${busy?'disabled':''}>${Array.from({length:(zeroPageOnly()?0:generated)+1},(_,r)=>`<option value="${r}" ${r===current?'selected':''}>${t(`第 ${r} 页`,`Page ${r}`)}</option>`).join('')}</select></div><div class="evolution-view-controls" ${zeroPageOnly()?'hidden':''}>${construction?`<button data-evolve="replay" ${busy?'disabled':''}>${t('重播生成','Replay')} ${math(`E_{${construction.r+1}}`)}</button>`:''}<button class="evolution-generate" data-evolve="next" ${busy?'disabled':''}>${t('取上同调 → ','Cohomology → ')+math(`E_{${current+1}}`)}</button></div>`;
 }
 const wait=ms=>new Promise(resolve=>setTimeout(resolve,reduced.matches?0:ms));
 function cancel(){
  token++;
  if(transformAnimation&&transformAnimation.playState!=='finished'){
   const frame=getComputedStyle(diagram).transform;transformAnimation.cancel();diagram.style.transform=frame;transformTarget='';
  }
  transformAnimation=null;layerAnimations.forEach(a=>a.cancel());layerAnimations=[];busy=false;construction=null;
 }
 async function beginCohomology(r=current){
  cancel();const run=token,needTilt=!tilted;current=r;start=Math.max(0,r-geometry().count+2);tilted=true;busy=true;projectionKey='';fit(needTilt);drawPages();paintControls();exposition();
  if(needTilt){await wait(1400);if(run!==token)return;}
  const goal=r+1;generated=Math.max(generated,goal);current=goal;start=Math.max(0,goal-geometry().count+1);construction={r,phase:3};projectionKey='';
  drawPages(goal);paintControls();exposition();
  await wait(1850);if(run!==token)return;busy=false;drawPages();paintControls();
 }
 function sync(s){
  context=s;
  const choice=s.annotationStep||1,wasEngaged=engaged;
  const eligible=!s.cover&&(s.module==='initial'&&s.initialReveal===8||s.module==='learn'&&(s.step===3||s.step===4||s.step===5&&choice>=3));
  engaged=eligible;toolbar.hidden=!eligible;overlay.hidden=!eligible;viewport.classList.toggle('has-evolution',eligible);controls.closest('.visualization-module').classList.toggle('page-evolution-mode',eligible);
  if(!eligible){if(wasEngaged){cancel();tilted=false;semanticKey='';fit();}if(s.cover){generated=0;current=0;start=0;proof.reset();}else if(s.module==='learn'&&s.step===5&&choice>=3)proof.render({state:s,current:Math.max(1,s.r),construction:null,point});window.spectralEvolution={engaged:false,tilted:false,generated,current,start,busy:false,construction:null};return;}
  const key=`${s.module}:${s.step}`;if(s.selected)point={...s.selected};
  if(key!==semanticKey){semanticKey=key;cancel();
   if(s.module==='initial'||s.module==='learn'&&s.step===3){tilted=false;current=0;start=0;fit(true);}
   else if(generated===0){beginCohomology(0);}
   else{current=Math.min(generated,s.step===4?1:Math.max(1,s.r));construction=current>0?{r:current-1,phase:3}:null;start=Math.max(0,current-geometry().count+1);tilted=true;fit(true);}
  }
  drawPages();paintControls();exposition();
 }
 toolbar.addEventListener('click',e=>{
  const button=e.target.closest('[data-evolve]');if(!button)return;const action=button.dataset.evolve;
  if(action==='next'&&!busy&&!zeroPageOnly()){beginCohomology();return;}if(action==='replay'&&construction&&!busy){beginCohomology(construction.r);return;}
  if(['flat','tilt'].includes(action)){cancel();tilted=action!=='flat';current=0;start=0;projectionKey='';fit(true);drawPages();paintControls();exposition();}
 });
 toolbar.addEventListener('change',e=>{if(e.target.id==='evolutionPage'){cancel();current=Number(e.target.value);construction=current>0?{r:current-1,phase:3}:null;start=Math.max(0,current-geometry().count+1);tilted=true;fit(true);drawPages();exposition();paintControls();}});
 const select=e=>{const target=e.target.closest('[data-page]');if(!target||busy)return;const selectedPage=Number(target.dataset.page);if(!construction||![construction.r,construction.r+1].includes(selectedPage)){current=selectedPage;construction=current>0?{r:current-1,phase:3}:null;}if(target.dataset.p!==undefined)point={p:Number(target.dataset.p),q:Number(target.dataset.q)};drawPages();paintControls();exposition();};

 overlay.addEventListener('click',select);overlay.addEventListener('keydown',e=>{if(e.key===' '){e.preventDefault();e.stopPropagation();select(e);}});
 new ResizeObserver(()=>{projectionKey='';fit();if(engaged)drawPages();}).observe(viewport);
 reduced.addEventListener('change',e=>{if(e.matches){transformAnimation?.finish();layerAnimations.forEach(a=>a.finish());}});
 return {sync,isTilted:()=>engaged&&tilted};
}
