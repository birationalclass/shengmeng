// A quiet outline of the reading sequence, independent of diagram interactions.
export function createReadingRail({workspace,column,mobilePane,content,language,cancelFollow}) {
 const rail=document.createElement('nav');rail.className='reading-rail';rail.hidden=true;
 const track=document.createElement('div');track.className='reading-rail-track';rail.append(track);workspace.append(rail);
 const narrow=matchMedia('(max-width:780px)');
 let items=[],hover=-1,visibleIndex=-1,frame=0,shown=false;
 const pane=()=>narrow.matches?mobilePane:column;
 const key=el=>`${el.closest('[data-statement]').dataset.statement}:${el.dataset.build??el.dataset.readingPage}`;
 const available=el=>!el.closest('[hidden],.formal-statement[data-open="false"]')&&el.getClientRects().length>0;
 function paint(){
  frame=0;if(!shown)return;
  const viewport=pane().getBoundingClientRect(),columnBox=column.getBoundingClientRect();
  const top=Math.max(viewport.top,document.querySelector('.notebook-toolbar').getBoundingClientRect().bottom)+12;
  const bottom=Math.min(innerHeight,viewport.bottom)-12;
  const height=Math.min(400,Math.max(160,bottom-top));
  const inset=parseFloat(getComputedStyle(rail).getPropertyValue('--reading-rail-inset'))||0;
  rail.style.left=`${Math.max(0,(narrow.matches?mobilePane.getBoundingClientRect().left:columnBox.left)+inset)}px`;
  rail.style.top=`${top+Math.max(0,(bottom-top-height)/2)}px`;rail.style.height=`${height}px`;
  const readingLine=Math.max(viewport.top,top)+viewport.height*.22;
  let nearest=-1,distance=Infinity;
  items.forEach((item,i)=>{
   const seen=available(item.el);item.button.classList.toggle('is-revealed',seen);
   if(!seen)return;
   const r=item.el.getBoundingClientRect(),d=readingLine<r.top?r.top-readingLine:readingLine>r.bottom?readingLine-r.bottom:0;
   if(d<distance){distance=d;nearest=i;}
  });
  visibleIndex=nearest;paintTicks();
 }
 function paintTicks(){
  items.forEach((item,i)=>{
   const distance=Math.abs(i-(hover>=0?hover:visibleIndex));
   item.button.style.setProperty('--rail-tick-width',`${distance===0?27:distance===1?20:distance===2?14:8}px`);
   if(i===visibleIndex)item.button.setAttribute('aria-current','location');else item.button.removeAttribute('aria-current');
  });
 }
 function schedule(){if(!frame)frame=requestAnimationFrame(paint);}
 function sync(){
  shown=!workspace.classList.contains('is-cover');rail.hidden=!shown;if(!shown)return;
  rail.setAttribute('aria-label',language()==='en'?'Reading outline':'阅读导航');
  const old=new Map(items.map(item=>[item.key,item]));
  items=[...content.querySelectorAll('.build-card,.numbered-entry')].map(el=>{
   const id=key(el),select=el.querySelector('[data-select-build],[data-select-reading]'),number=el.querySelector('.statement-subnumber').textContent;
   const item=old.get(id)||{key:id,button:document.createElement('button')};
   item.el=el;item.select=select;item.button.type='button';item.button.className='reading-rail-mark';item.button.dataset.readingKey=id;
   const caption=`<span class="reading-rail-caption" aria-hidden="true"><span>${number}</span> ${select.innerHTML}</span>`;
   const html='<span class="reading-rail-tick" aria-hidden="true"></span>'+caption;
   if(item.button.innerHTML!==html)item.button.innerHTML=html;
   const title=select.cloneNode(true);title.querySelectorAll('.katex').forEach(math=>math.replaceWith(math.querySelector('annotation')?.textContent||math.textContent));
   item.button.setAttribute('aria-label',`${number} ${title.textContent.trim()}`);
   track.append(item.button);old.delete(id);return item;
  });
  for(const item of old.values())item.button.remove();
  if(hover>=items.length)hover=-1;schedule();
 }
 track.addEventListener('click',event=>{
  const button=event.target.closest('.reading-rail-mark'),item=items.find(item=>item.button===button);
  if(item)item.select.click();
 });
 track.addEventListener('pointermove',event=>{
  const i=items.findIndex(item=>item.button===event.target.closest('.reading-rail-mark'));
  if(i!==hover){hover=i;paintTicks();}
 });
 rail.addEventListener('pointerleave',()=>{hover=-1;paintTicks();});
 rail.addEventListener('wheel',event=>{
  if(event.ctrlKey||!event.deltaY)return;
  event.preventDefault();cancelFollow();const scrollport=pane();
  const unit=event.deltaMode===1?16:event.deltaMode===2?scrollport.clientHeight:1;
  scrollport.scrollTop+=event.deltaY*unit;
 },{passive:false});
 for(const scrollport of new Set([column,mobilePane]))scrollport.addEventListener('scroll',schedule,{passive:true});
 window.addEventListener('resize',schedule);document.addEventListener('fullscreenchange',schedule);narrow.addEventListener('change',schedule);
 const observer=new ResizeObserver(schedule);observer.observe(content);observer.observe(column);observer.observe(mobilePane);
 return {sync};
}
