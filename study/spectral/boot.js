// Small, dependency-free bootstrap: never reveal untypeset content on failure.
(()=>{
 const overlay=document.getElementById('mathLoader'),status=document.getElementById('loaderStatus'),bar=overlay.querySelector('[role=progressbar]');
 let done=false,failed=false;
 const en=()=>localStorage.getItem('spectral-language')==='en';
 const progress=(value,zh,english)=>{if(done||failed)return;bar.setAttribute('aria-valuenow',value);bar.firstElementChild.style.width=value+'%';status.textContent=en()?english:zh;};
 const fail=()=>{if(done)return;failed=true;status.textContent=en()?'Unable to load mathematics':'数学资源加载失败';document.getElementById('loaderRetry').hidden=false;};
 const ready=()=>{if(failed)return;done=true;document.documentElement.classList.remove('math-loading');document.body.setAttribute('aria-busy','false');overlay.classList.add('is-ready');overlay.addEventListener('transitionend',()=>{overlay.hidden=true;},{once:true});if(matchMedia('(prefers-reduced-motion:reduce)').matches)overlay.hidden=true;};
 document.getElementById('loaderRetry').onclick=()=>location.reload();
 window.spectralBoot={progress,ready,fail};
 window.addEventListener('error',event=>{if(!done&&(event.target?.tagName==='SCRIPT'||event.message))fail();},true);
 window.addEventListener('unhandledrejection',()=>{if(!done)fail();});
 progress(30,'加载数学资源','Loading mathematics');
})();
