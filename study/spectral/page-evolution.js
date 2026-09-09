// The existing two-dimensional diagram is the physical E0 plane.
// Its affine projection changes only the view. Further pages are cohomology objects.
export function createPageEvolution({origin,viewport,diagram,controls,board,math,language}){
 const R=String.raw,t=(zh,en)=>language()==='en'?en:zh,reduced=matchMedia('(prefers-reduced-motion:reduce)');
 const overlay=document.createElement('div');overlay.id='pageEvolution';overlay.hidden=true;viewport.append(overlay);
 const toolbar=document.createElement('nav');toolbar.id='evolutionControls';toolbar.hidden=true;controls.prepend(toolbar);
 let context=null,engaged=false,tilted=false,generated=0,current=0,start=0,semanticKey='',token=0,busy=false,manualBoard=false,point={p:1,q:2},transformAnimation=null,scale=1,projectionKey='',transformTarget='',layerAnimations=[];
 const compact=()=>matchMedia('(max-width:780px)').matches;
 const geometry=()=>compact()?{x:110,y:360,dp:55,dq:64,yp:24,dr:400,count:2}:{x:55,y:345,dp:35,dq:54,yp:26,dr:210,count:4};
 const pos=(p,q,r)=>{const g=geometry();return [g.x+g.dp*p+g.dr*(r-start),g.y+g.yp*p-g.dq*q];};
 const color=r=>['#8fbeff','#71e2d0','#f4c876','#d9b7ec'][r%4];
 // Hand off the whole source layer only when its projection has reached the
 // destination. Crossfading earlier would draw E0 in two different positions.
 function settleProjection(){
  const ready=engaged&&tilted;
  diagram.classList.toggle('evolution-settled',ready);
  overlay.classList.toggle('is-tilted',ready);
  diagram.inert=ready;
 }
 function fit(animate=false){
  const bounds=viewport.getBoundingClientRect(),width=Math.min(bounds.width,bounds.height*840/525);scale=width/840;overlay.style.width=width+'px';overlay.style.height=width*525/840+'px';
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
 function pageMarkup(r){
  const g=geometry(),c=color(r),corners=[[0,0],[4,0],[4,4],[0,4]].map(([p,q])=>pos(p,q,r).join(',')).join(' '),origin=pos(0,0,r);
  let out=`<g class="evolution-page ${r===current?'is-current':''}" data-r="${r}" style="--evolution-color:${c}"><polygon class="evolution-sheet" points="${corners}"/>`;
  for(let i=0;i<=4;i++){const a=pos(i,0,r),b=pos(i,4,r),c=pos(0,i,r),d=pos(4,i,r);out+=`<path class="evolution-grid" d="M${a} L${b} M${c} L${d}"/>`;}
  for(let p=0;p<=4;p++)for(let q=0;q<=4;q++){const [x,y]=pos(p,q,r),selected=p===point.p&&q===point.q;out+=`<g class="evolution-point ${selected?'is-selected':''}" role="button" tabindex="${selected?'0':'-1'}" data-page="${r}" data-p="${p}" data-q="${q}" aria-label="E_${r}^{${p},${q}}"><circle class="evolution-hit" cx="${x}" cy="${y}" r="10"/><circle class="evolution-dot" cx="${x}" cy="${y}" r="${selected?5:2.8}"/></g>`;}
  const [p,q]=[point.p,point.q],tp=p+r,tq=q-r+1,source=pos(p,q,r);
  if(tp<=4&&tq>=0&&tq<=4){const target=pos(tp,tq,r),dx=target[0]-source[0],dy=target[1]-source[1],len=Math.hypot(dx,dy);out+=`<path class="evolution-differential" data-source="${p},${q},${r}" data-target="${tp},${tq},${r}" d="M${source[0]+dx*9/len},${source[1]+dy*9/len} L${target[0]-dx*9/len},${target[1]-dy*9/len}" marker-end="url(#evolution-tip-${r%4})"/><text class="evolution-d-label" x="${(source[0]+target[0])/2+8}" y="${(source[1]+target[1])/2-8}">d<tspan baseline-shift="sub" font-size="12">${r}</tspan></text>`;}
  out+=`<text class="evolution-point-label" x="${source[0]-51}" y="${source[1]+5}">E<tspan baseline-shift="sub" font-size="13">${r}</tspan><tspan baseline-shift="super" font-size="12">${p},${q}</tspan></text>`;
  out+=`<g role="button" tabindex="0" data-page="${r}" class="evolution-page-title" aria-label="E_${r}"><rect x="${origin[0]-12}" y="37" width="${g.dp*4+24}" height="39" rx="8"/><text x="${origin[0]+g.dp*2}" y="65" text-anchor="middle">E<tspan baseline-shift="sub" font-size="15">${r}</tspan></text></g><text class="evolution-r-tick" x="${origin[0]}" y="${g.y+24}" text-anchor="middle">${r}</text></g>`;
  return out;
 }
 function drawPages(newPage=null){
  const g=geometry();start=Math.max(0,Math.min(start,Math.max(0,generated-g.count+1)));
  if(current<start)start=current;else if(current>=start+g.count)start=current-g.count+1;
  const key=[start,Math.min(generated,start+g.count-1),current,point.p,point.q,language(),compact()].join(':');
  if(key!==projectionKey){
   let out='<svg viewBox="0 0 840 525" role="group" aria-label="'+t('由二维 E0 连续展开的谱序列各页','Spectral-sequence pages unfolding from the original two-dimensional E0')+'"><defs>';
   for(let i=0;i<4;i++)out+=`<marker id="evolution-tip-${i}" markerUnits="userSpaceOnUse" markerWidth="9" markerHeight="9" refX="7" refY="4.5" orient="auto"><path d="M1.5,1.5 L7,4.5 L1.5,7.5" fill="none" stroke="${color(i)}" stroke-width="1.3"/></marker>`;
   out+=`</defs><path class="evolution-r-axis" d="M28,${g.y} H817" marker-end="url(#evolution-tip-0)"/><text class="evolution-axis-label" x="815" y="${g.y-12}">r</text>`;
   if(start>0)out+=`<text class="evolution-axis-label" x="10" y="${g.y-9}">⋯</text>`;
   for(let r=start;r<=Math.min(generated,start+g.count-1);r++)out+=pageMarkup(r);
   const pAxis=pos(4.6,0,start),qAxis=pos(0,4.5,start),o=pos(0,0,start);
   out+=`<path class="evolution-r-axis" d="M${o} L${pAxis} M${o} L${qAxis}"/>`;
   out+=`<text class="evolution-axis-label" x="${pAxis[0]+8}" y="${pAxis[1]}">p</text><text class="evolution-axis-label" x="${qAxis[0]-18}" y="${qAxis[1]}">q</text></svg>`;
   overlay.innerHTML=out;projectionKey=key;
   if(newPage!==null&&!reduced.matches){const page=overlay.querySelector(`[data-r="${newPage}"]`);if(page){const animation=page.animate([{opacity:0,transform:`translateX(${-g.dr}px)`},{opacity:1,transform:'translateX(0)'}],{duration:850,easing:'cubic-bezier(.22,.68,.18,1)'});layerAnimations.push(animation);}}
  }
  fit();window.spectralEvolution={engaged,tilted,generated,current,start,busy,point:{...point}};
 }
 function exposition(){
  const line=f=>`<div class="operation-equation">${math(f,true)}</div>`;let equations,note;
  if(!tilted&&context.module==='learn'){equations=[R`E_0^{p,q}\cong K^{p,q},\qquad d_0[a]=[Da]\leftrightarrow\delta_2a`,R`E_1^{p,q}=H^q(E_0^{p,\bullet},d_0)=H^q(K^{p,\bullet},\delta_2)`];note=t('δ₁ 的像落入下一列，在关联分次中为零；δ₂ 保持列，诱导 d₀。','The image of δ₁ lies in the next column and vanishes in the associated graded; δ₂ preserves the column and induces d₀.');}
  else if(!tilted){equations=[R`E_0^{p,q}:=\operatorname{Gr}_F^pC^{p+q}=F^pC^{p+q}/F^{p+1}C^{p+q}`,R`F^pC^{p+q}=K^{p,q}\oplus F^{p+1}C^{p+q}\quad\Longrightarrow\quad E_0^{p,q}\cong K^{p,q}`];note=t('取第 p 列分量给出自然同构；同一坐标处的 K 与 E₀ 对应。','Projection to column p gives the natural isomorphism: K and E₀ correspond at the same coordinates.');}
  else if(current===0){equations=[R`E_0^{p,q}\cong K^{p,q},\qquad d_0^{p,q}\leftrightarrow\delta_2^{p,q}`,R`E_1^{p,q}=H^q(E_0^{p,\bullet},d_0)`];note=t('倾斜只改变视角，E₀ 及 d₀ 不变。生成下一页时，才对 (E₀,d₀) 取上同调。','Tilting changes only the viewpoint; E₀ and d₀ are unchanged. The next page is obtained by taking cohomology of (E₀,d₀).');}
  else{const r=current-1,shift=(name,n)=>n===0?name:`${name}${n>0?'+':''}${n}`;equations=[R`E_{${current}}^{p,q}\cong\frac{\ker(d_{${r}}:E_{${r}}^{p,q}\to E_{${r}}^{${shift('p',r)},${shift('q',1-r)}})}{\operatorname{im}(d_{${r}}:E_{${r}}^{${shift('p',-r)},${shift('q',r-1)}}\to E_{${r}}^{p,q})}`,R`d_{${current}}:E_{${current}}^{p,q}\longrightarrow E_{${current}}^{${shift('p',current)},${shift('q',1-current)}}`];note=t('新平面表示上一页的上同调；新页上的 dᵣ 仍由滤过总微分 D 诱导。层间没有整页的线性映射。','The new plane represents the preceding page’s cohomology. Its dᵣ is still induced by the filtered total differential D; no whole-page linear map is implied.');}
  board.innerHTML=`<div class="operation-content evolution-exposition">${equations.map(line).join('')}</div><p class="operation-note">${note}</p>`;
 }
 function paintControls(){
  toolbar.hidden=!engaged;
  toolbar.innerHTML=`<button data-evolve="flat" aria-pressed="${!tilted}">${t('二维 E₀','2D E₀')}</button><button data-evolve="tilt" aria-pressed="${tilted}">${t('倾斜 E₀','Tilt E₀')}</button><button class="evolution-generate" data-evolve="next" ${busy?'disabled':''}>${busy?t('生成中…','Forming…'):t('生成 ','Form ')+`E${subscript(generated+1)}`}</button><span class="evolution-pages">${t('查看','Inspect')} <button data-window="-1" ${start===0?'disabled':''}>‹</button><select id="evolutionPage" aria-label="${t('查看已生成的页','Inspect a generated page')}">${Array.from({length:generated+1},(_,r)=>`<option value="${r}" ${r===current?'selected':''}>E${subscript(r)}</option>`).join('')}</select><button data-window="1" ${start+geometry().count>generated?'disabled':''}>›</button></span>`;
 }
 const subscript=n=>String(n).replace(/\d/g,x=>'₀₁₂₃₄₅₆₇₈₉'[+x]);
 const wait=ms=>new Promise(resolve=>setTimeout(resolve,reduced.matches?0:ms));
 function cancel(){
  token++;
  if(transformAnimation&&transformAnimation.playState!=='finished'){
   const frame=getComputedStyle(diagram).transform;transformAnimation.cancel();diagram.style.transform=frame;transformTarget='';
  }
  transformAnimation=null;layerAnimations.forEach(a=>a.cancel());layerAnimations=[];busy=false;
 }
 async function unfold(goal){
  const run=++token;busy=true;manualBoard=context.module!=='converge'||manualBoard;
  if(!tilted){tilted=true;current=0;start=0;fit(true);drawPages();paintControls();if(context.module!=='converge'||manualBoard)exposition();await wait(1100);if(run!==token)return;}
  while(generated<goal){generated++;current=generated;start=Math.max(0,generated-geometry().count+1);projectionKey='';drawPages(generated);paintControls();if(context.module!=='converge'||manualBoard)exposition();await wait(880);if(run!==token)return;}
  busy=false;current=goal;start=Math.max(0,current-geometry().count+1);drawPages();paintControls();if(context?.module!=='converge'||manualBoard)exposition();
 }
 function sync(s){
  context=s;const wasEngaged=engaged,eligible=!s.cover&&(s.module==='initial'&&s.initialReveal===8||['learn','converge'].includes(s.module));engaged=eligible;toolbar.hidden=!eligible;overlay.hidden=!eligible;viewport.classList.toggle('has-evolution',eligible);
  if(!eligible){if(wasEngaged){cancel();tilted=false;semanticKey='';fit(true);}else fit();window.spectralEvolution={engaged:false,tilted:false,generated,current,start,busy:false};return;}
  const choice=s.pinnedKey?.startsWith('formula:')?Number(s.pinnedKey.split(':')[1])+1:s.chosenAction||1,key=`${s.module}:${s.step}:${choice}`;
  if(s.selected)point={...s.selected};
  if(key!==semanticKey){semanticKey=key;manualBoard=false;cancel();
   if(s.module==='initial'){tilted=false;current=0;start=0;fit(true);}
   else if(s.module==='learn'&&s.step===3&&choice===1){current=0;start=0;fit(true);}
   else{const goal=s.module==='learn'?s.step===3?1:s.step===4?(choice>=3?2:1):Math.max(1,s.r)+(choice===5?1:0):Math.max(2,generated);unfold(goal);}
  }
  drawPages();paintControls();if(s.module!=='converge'||manualBoard)exposition();
 }
 toolbar.addEventListener('click',e=>{const button=e.target.closest('[data-evolve]'),windowButton=e.target.closest('[data-window]');if(button){manualBoard=true;const action=button.dataset.evolve;if(action==='flat'){cancel();tilted=false;current=0;start=0;fit(true);drawPages();paintControls();exposition();}else if(action==='tilt'){cancel();tilted=true;current=0;start=0;fit(true);drawPages();paintControls();exposition();}else if(!busy)unfold(generated+1);}if(windowButton){start=Math.max(0,Math.min(Math.max(0,generated-geometry().count+1),start+Number(windowButton.dataset.window)*geometry().count));current=start;manualBoard=true;drawPages();paintControls();exposition();}});
 toolbar.addEventListener('change',e=>{if(e.target.id==='evolutionPage'){current=Number(e.target.value);start=Math.max(0,current-geometry().count+1);tilted=true;manualBoard=true;fit(true);drawPages();exposition();paintControls();}});
 const select=e=>{const target=e.target.closest('[data-page]');if(!target)return;current=Number(target.dataset.page);if(target.dataset.p!==undefined)point={p:Number(target.dataset.p),q:Number(target.dataset.q)};manualBoard=true;drawPages();paintControls();exposition();};overlay.addEventListener('click',select);overlay.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();e.stopPropagation();select(e);}});
 new ResizeObserver(()=>{projectionKey='';fit();if(engaged)drawPages();}).observe(viewport);
 reduced.addEventListener('change',e=>{if(e.matches){transformAnimation?.finish();layerAnimations.forEach(a=>a.finish());}});
 return {sync,isTilted:()=>engaged&&tilted};
}
