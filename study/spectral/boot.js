// One cover for loading and entry. Typesetting never advances into the lesson.
(()=>{
 const overlay=document.getElementById('mathLoader'),status=document.getElementById('loaderStatus'),bar=overlay.querySelector('[role=progressbar]'),start=document.getElementById('beginSlides');
 let done=false,failed=false;
 const en=()=>localStorage.getItem('spectral-language')==='en';
 const progress=(value,zh,english)=>{if(done||failed)return;bar.setAttribute('aria-valuenow',value);bar.firstElementChild.style.width=value+'%';status.textContent=en()?english:zh;};
 const fail=()=>{if(done)return;failed=true;status.textContent=en()?'Unable to load mathematics':'数学资源加载失败';document.getElementById('loaderRetry').hidden=false;};
 const showCover=()=>{
  overlay.hidden=false;overlay.classList.remove('is-ready');document.documentElement.classList.add('math-loading');
  if(done){start.disabled=false;start.hidden=false;start.innerHTML=en()?'Start reading <span>→</span>':'开始阅读 <span>→</span>';status.textContent=en()?'READY':'准备就绪';}
 };
 const ready=()=>{if(failed)return;done=true;document.body.setAttribute('aria-busy','false');overlay.classList.add('awaiting-entry');bar.setAttribute('aria-hidden','true');showCover();};
 const enter=()=>{
  if(!done||failed)return false;
  start.disabled=true;document.documentElement.classList.remove('math-loading');overlay.classList.add('is-ready');
  if(matchMedia('(prefers-reduced-motion:reduce)').matches)overlay.hidden=true;
  return true;
 };
 overlay.addEventListener('transitionend',e=>{if(e.target===overlay&&e.propertyName==='opacity'&&overlay.classList.contains('is-ready'))overlay.hidden=true;});
 document.getElementById('loaderRetry').onclick=()=>location.reload();
 window.spectralBoot={progress,ready,fail,enter,showCover};
 window.addEventListener('error',event=>{if(!done&&(event.target?.tagName==='SCRIPT'||event.message))fail();},true);
 window.addEventListener('unhandledrejection',()=>{if(!done)fail();});
 progress(30,'加载数学资源','Loading mathematics');
})();
