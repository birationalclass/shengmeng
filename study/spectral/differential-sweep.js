// A page-by-page bidegree demonstration. All geometry uses the fixed grid frame.
export function createDifferentialSweep({host,point,math}){
 let layer=null,base=[],animations=[],serial=0,settle=()=>{};
 const reduced=()=>matchMedia('(prefers-reduced-motion:reduce)').matches;
 const animate=(el,frames,duration)=>{const a=el.animate(frames,{duration:reduced()?0:duration,fill:'both',easing:'cubic-bezier(.4,0,.2,1)'});animations.push(a);return a.finished.catch(()=>{});};
 function clear({keep=false}={}){
  serial++;
  if(keep&&layer){settle();return;}
  animations.forEach(a=>a.cancel());animations=[];
  const old=layer;layer=null;
  base.forEach(([el,opacity])=>{el.style.opacity=opacity;});base=[];
  if(old){old.removeAttribute('id');old.animate([{opacity:1},{opacity:0}],{duration:reduced()?0:200,fill:'forwards'}).finished.then(()=>old.remove(),()=>old.remove());}
 }
 function text(x,y,tex,cls=''){
  const el=document.createElement('div');el.className='dr-sweep-label '+cls;el.style.left=x+'px';el.style.top=y+'px';el.innerHTML=math(tex);layer.append(el);return el;
 }
 async function play({signal,wait}){
  clear();const run=serial;
  layer=document.createElement('div');layer.id='differentialSweep';layer.className='dr-sweep';layer.setAttribute('aria-hidden','true');
  layer.innerHTML='<svg viewBox="0 0 840 525"><defs><marker id="dr-sweep-tip" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M1 1L8 5L1 9" fill="none" stroke="#f2c56e" stroke-width="1.3"/></marker></defs><path class="dr-sweep-arrow" marker-end="url(#dr-sweep-tip)"/></svg>';
  const cells=[];for(let p=0;p<=4;p++)for(let q=0;q<=4;q++){
   const [x,y]=point(p,q);const el=text(x,y,`E_0^{${p},${q}}`,'dr-sweep-cell');el.dataset.p=p;el.dataset.q=q;
   // Typeset the base and superscript once; only opacity in the fixed digit slot changes.
   const slot=el.querySelector('.katex-html .msupsub .vlist > span .sizing > .mord');
   slot.classList.add('dr-page-slot');slot.innerHTML='<span class="dr-page-reserve">0</span>'+Array.from({length:6},(_,r)=>`<span class="dr-page-digit" data-page="${r}" style="opacity:${r===0?1:0}">${r}</span>`).join('');
   cells.push({p,q,el,digits:[...slot.querySelectorAll('.dr-page-digit')]});
  }
  const [sx,sy]=point(0,3),page=text(420,22,'r=0'),arrowLabel=text(sx+27,(sy+point(0,4)[1])/2,'d_0^{0,3}','dr-sweep-map');
  const [zx,zy]=point(5,-1),zero=text(zx,zy,'0','dr-sweep-zero'),reason=text(640,22,'E_5^{5,-1}=0','dr-sweep-reason');zero.style.opacity=reason.style.opacity='0';
  const path=layer.querySelector('.dr-sweep-arrow');
  let position=0;
  function geometry(v){position=v;const [tx,ty]=point(v,4-v),dx=tx-sx,dy=ty-sy,len=Math.hypot(dx,dy),pad=Math.min(len/2-3,Math.min(dx===0?Infinity:34*len/Math.abs(dx),dy===0?Infinity:19*len/Math.abs(dy))+5);path.setAttribute('d',`M${sx+dx*pad/len},${sy+dy*pad/len} L${tx-dx*pad/len},${ty-dy*pad/len}`);// Offset along the upper normal, reserving the formula's projected half-size.
   // Both label and path stay in the same grid coordinates at every animation frame.
   const nx=dy/len,ny=-dx/len,gap=10+Math.abs(nx)*arrowLabel.offsetWidth/2+Math.abs(ny)*arrowLabel.offsetHeight/2;
   arrowLabel.style.left=((sx+tx)/2+nx*gap)+'px';arrowLabel.style.top=((sy+ty)/2+ny*gap)+'px';}
  function highlight(r){for(const c of cells)c.el.classList.toggle('is-selected',c.p===0&&c.q===3||c.p===r&&c.q===4-r);}
  settle=()=>{const r=Number(layer.dataset.r)||0,from=position,start=performance.now(),retained=layer;page.innerHTML=math(`r=${r}`);arrowLabel.innerHTML=math(`d_${r}^{0,3}`);const finish=now=>{if(layer!==retained)return;const t=reduced()?1:Math.min(1,(now-start)/220);geometry(from+(r-from)*t*t*(3-2*t));if(t<1)requestAnimationFrame(finish);};requestAnimationFrame(finish);};
  host.append(layer);geometry(0);highlight(0);
  base=[...host.querySelectorAll(':scope > svg,:scope > .diagram-label-plane')].map(el=>[el,el.style.opacity]);
  await Promise.all([animate(layer,[{opacity:0},{opacity:1}],300),...base.map(([el])=>animate(el,[{opacity:1},{opacity:0}],300))]);
  const live=()=>!signal.aborted&&serial===run;
  function publish(r,phase){layer.dataset.r=r;window.spectralDifferentialSweep={r,phase,source:[0,3],target:[r,4-r],zero:r===5};}
  publish(0,'holding');
  for(let r=1;r<=5;r++){
   if(!await wait(1000)||!live())return;
   const digitChanges=[];for(const {p,q,el,digits}of cells){
    digitChanges.push(animate(digits[r-1],[{opacity:1},{opacity:0}],420),animate(digits[r],[{opacity:0},{opacity:1}],420));
    el.querySelector('.katex-mathml msubsup > mn').textContent=r;
    el.querySelector('.katex-mathml annotation').textContent=`E_${r}^{${p},${q}}`;
   }
   const change=async(el,tex)=>{await animate(el,[{opacity:1},{opacity:0}],180);if(live()){el.innerHTML=math(tex);await animate(el,[{opacity:0},{opacity:1}],240);}};
   const labels=Promise.all([change(page,`r=${r}`),change(arrowLabel,`d_${r}^{0,3}`),...digitChanges]);
   highlight(r);publish(r,'transition');
   await new Promise(resolve=>{const start=performance.now();const tick=now=>{if(!live())return resolve();const t=reduced()?1:Math.min(1,(now-start)/850),e=t*t*(3-2*t);geometry(r-1+e);if(t<1)requestAnimationFrame(tick);else resolve();};requestAnimationFrame(tick);});
   await labels;if(!live())return;
   if(r===5)await Promise.all([animate(zero,[{opacity:0},{opacity:1}],300),animate(reason,[{opacity:0},{opacity:1}],300)]);
   publish(r,'holding');
  }
  if(await wait(1000)&&live())publish(5,'complete');
 }
 return {play,clear};
}
