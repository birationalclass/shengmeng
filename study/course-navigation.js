// Stable subsection/part links and cooperative same-origin tab reuse.
export function installCourseNavigation({course,language,entries,current,navigate}) {
 const en=()=>language()==='en',say=(zh,english)=>en()?english:zh;
 const id=globalThis.crypto?.randomUUID?.()||String(Math.random());
 const peers=new Map(),pending=new Map();let channel=null,ready=false;
 const locationFor=(entry,part=1)=>`#entry=${encodeURIComponent(entry)}&part=${Math.max(1,Number(part)||1)}`;
 const parse=hash=>{const p=new URLSearchParams(hash.replace(/^#/,''));return p.has('entry')?{entry:p.get('entry'),part:Number(p.get('part'))||1}:null;};
 const link=(target,entry,part)=>new URL(`../${target}/${locationFor(entry,part)}`,location.href).href;
 const announce=()=>channel?.postMessage({type:'present',id,course,time:Date.now()});
 async function locate(value){if(!ready)return false;const item=entries().find(e=>e.entry===value.entry);if(!item)return false;const part=Math.min(item.parts||1,Math.max(1,value.part||1));await navigate(item,part);history.replaceState(null,'',locationFor(item.entry,part));return true;}
 try{channel=new BroadcastChannel('math-notebook-navigation-v1');channel.onmessage=async({data:m})=>{
  if(!m||m.id===id)return;
  if(m.type==='hello'){announce();return;}
  if(m.type==='present'){peers.set(m.id,{...m,seen:Date.now()});return;}
  if(m.type==='bye'){peers.delete(m.id);return;}
  if(m.type==='located'&&m.target===id){clearTimeout(pending.get(m.request));pending.delete(m.request);return;}
  if(m.type==='locate'&&m.target===id&&ready&&entries().some(e=>e.entry===m.entry)){channel.postMessage({type:'located',id,target:m.id,request:m.request});await locate(m);window.focus();announce();}
 };channel.postMessage({type:'hello',id});announce();}catch{}
 const presence=setInterval(announce,4000);
 window.addEventListener('pagehide',()=>{channel?.postMessage({type:'bye',id});clearInterval(presence);});
 window.addEventListener('pageshow',announce);
 window.addEventListener('focus',announce);
 // A named target is also reused when cooperative messaging is unavailable.
 window.name=`math-notebook-${course}`;
 document.addEventListener('click',event=>{
  const a=event.target.closest('a[data-course-link]');if(!a||event.button||event.metaKey||event.ctrlKey||event.shiftKey||event.altKey)return;
  const url=new URL(a.href,location.href),value=parse(url.hash);if(!value)return;
  const target=url.pathname.match(/\/study\/(spectral|mhs)\//)?.[1];if(!target)return;
  if(url.origin===location.origin&&target===course){event.preventDefault();locate(value);return;}
  if(url.origin!==location.origin)return;
  const existing=[...peers.values()].filter(p=>p.course===target&&Date.now()-p.seen<15000).sort((a,b)=>b.time-a.time)[0];
  if(existing){event.preventDefault();const request=String(Math.random());
   pending.set(request,setTimeout(()=>{pending.delete(request);peers.delete(existing.id);const opened=window.open(url.href,`math-notebook-${target}`);if(!opened){const fallback=document.createElement('a');fallback.href=url.href;fallback.target=`math-notebook-${target}`;fallback.className='course-navigation-fallback';fallback.textContent=say('打开引用条目 ↗','Open referenced entry ↗');document.body.append(fallback);fallback.onclick=()=>fallback.remove();}},450));
   channel.postMessage({type:'locate',id,target:existing.id,request,...value});
  }
 });
 const css=document.createElement('link');css.rel='stylesheet';css.href=new URL('./course-navigation.css',import.meta.url);document.head.append(css);
 const dialog=document.createElement('dialog');dialog.className='course-locator';document.body.append(dialog);
 const button=document.createElement('button');button.className='toolbar-icon course-locate-button';button.type='button';button.innerHTML='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" aria-hidden="true"><circle cx="12" cy="12" r="6"/><path d="M12 2v5m0 10v5M2 12h5m10 0h5"/></svg>';
 const sync=()=>{button.title=button.ariaLabel=say('定位到小节 / 复制定位链接','Locate subsection / copy link');};sync();document.querySelector('.toolbar-actions')?.prepend(button);
 new MutationObserver(sync).observe(document.documentElement,{attributes:true,attributeFilter:['lang']});
 const escape=text=>String(text).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
 button.onclick=()=>{
  const list=entries(),active=current();
  dialog.innerHTML=`<form method="dialog"><button class="locator-close" aria-label="${say('关闭','Close')}">×</button></form><h2>${say('定位','Locate')}</h2><label>${say('小节','Subsection')}<select class="locator-entry">${list.map(e=>`<option value="${e.entry}">${escape(e.entry+' '+e.title)}</option>`).join('')}</select></label><label>${say('条目','Item')}<select class="locator-part"></select></label><div class="locator-actions"><button type="button" class="locator-go">${say('前往','Go')}</button><button type="button" class="locator-copy">${say('复制定位链接','Copy location link')}</button></div><output></output><nav class="course-references"><a data-course-link href="${link(course==='mhs'?'spectral':'mhs','1.1',1)}" target="math-notebook-${course==='mhs'?'spectral':'mhs'}">${course==='mhs'?say('谱序列','Spectral Sequence'):'MHS'} ↗</a></nav>`;
  const select=dialog.querySelector('.locator-entry'),part=dialog.querySelector('.locator-part');select.value=active.entry;
  const update=()=>{const e=list.find(x=>x.entry===select.value)||list[0];part.innerHTML=Array.from({length:e.parts||1},(_,i)=>`<option>${i+1}</option>`).join('');};update();part.value=String(active.part||1);select.onchange=update;
  const value=()=>({entry:select.value,part:Number(part.value)||1});
  dialog.querySelector('.locator-go').onclick=()=>{dialog.close();locate(value());};
  dialog.querySelector('.locator-copy').onclick=async()=>{const v=value(),url=link(course,v.entry,v.part),out=dialog.querySelector('output');try{await navigator.clipboard.writeText(url);out.textContent=say('已复制','Copied');}catch{out.textContent=url;}};
  dialog.showModal();
 };
 window.addEventListener('hashchange',()=>{const v=parse(location.hash);if(v)locate(v);});
 return {link,async restore(hash){ready=true;announce();const v=parse(hash);if(v)await locate(v);},locate};
}
