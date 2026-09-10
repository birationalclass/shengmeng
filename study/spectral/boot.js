// One cover for loading and entry. Typesetting never advances into the lesson.
(()=>{
 const overlay=document.getElementById('mathLoader'),status=document.getElementById('loaderStatus'),bar=overlay.querySelector('[role=progressbar]'),start=document.getElementById('beginSlides');
 let done=false,failed=false,progressValue=0;
 const en=()=>localStorage.getItem('spectral-language')==='en';
 const coverFullscreen=document.getElementById('coverFullscreen'),lessonFullscreen=document.getElementById('fullscreen');
 let fullscreenScroll=0,fullscreenPending=false;
 const fullscreenActive=()=>document.body.classList.contains('study-fullscreen');
 const syncFullscreen=()=>{
  const active=fullscreenActive(),label=en()?(active?'Exit fullscreen':'Fullscreen'):(active?'退出全屏':'全屏');
  coverFullscreen.querySelector('span').textContent=label;lessonFullscreen.textContent='⛶ '+label;
  for(const button of [coverFullscreen,lessonFullscreen]){button.setAttribute('aria-pressed',String(active));button.setAttribute('aria-label',label);button.title=active?label+' (Esc)':label;button.disabled=fullscreenPending;}
 };
 const leaveFullscreen=()=>{
  document.body.classList.remove('study-fullscreen');syncFullscreen();window.scrollTo(0,fullscreenScroll);
  const button=!overlay.hidden&&!overlay.classList.contains('is-ready')?coverFullscreen:lessonFullscreen;
  button.focus({preventScroll:true});
 };
 const exitFullscreen=async()=>{
  if(document.fullscreenElement){try{await document.exitFullscreen();}catch{/* Preserve actual fullscreen state if the browser refuses an exit. */}}
  if(!document.fullscreenElement)leaveFullscreen();
 };
 const toggleFullscreen=async()=>{
  if(fullscreenPending)return;fullscreenPending=true;
  try{
   if(fullscreenActive()){syncFullscreen();await exitFullscreen();return;}
   fullscreenScroll=window.scrollY;document.body.classList.add('study-fullscreen');syncFullscreen();
   try{if(document.documentElement.requestFullscreen)await document.documentElement.requestFullscreen();}catch{/* Embedded browsers keep the viewport-filling study layout. */}
  }finally{fullscreenPending=false;syncFullscreen();}
 };
 coverFullscreen.onclick=toggleFullscreen;lessonFullscreen.onclick=toggleFullscreen;
 document.addEventListener('fullscreenchange',()=>{if(document.fullscreenElement){document.body.classList.add('study-fullscreen');syncFullscreen();}else if(fullscreenActive())leaveFullscreen();});
 document.addEventListener('keydown',e=>{if(e.key==='Escape'&&fullscreenActive()&&!document.querySelector('dialog[open]')){e.preventDefault();exitFullscreen();}});
 window.spectralFullscreen={sync:syncFullscreen};
 // Smooth only the visual interpolation; milestones still report real progress.
 const progress=(value,zh,english)=>{if(done||failed)return;progressValue=Math.max(progressValue,Math.min(100,Math.max(0,value)));bar.setAttribute('aria-valuenow',progressValue);bar.firstElementChild.style.transform=`scaleX(${progressValue/100})`;status.textContent=en()?english:zh;};
 const fail=()=>{if(done)return;failed=true;overlay.classList.add('loading-failed');status.textContent=en()?'Unable to load mathematics':'数学资源加载失败';document.getElementById('loaderRetry').hidden=false;};
 const showCover=()=>{
  overlay.hidden=false;overlay.classList.remove('is-ready');document.documentElement.classList.add('math-loading');
  overlay.querySelector('.loader-eyebrow').textContent=en()?'Study Notes':'学习笔记';syncFullscreen();
  if(done){start.disabled=false;start.hidden=false;start.innerHTML=en()?'Start reading <span>→</span>':'开始阅读 <span>→</span>';status.textContent='';status.setAttribute('aria-hidden','true');}
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
 overlay.querySelector('.loader-eyebrow').textContent=en()?'Study Notes':'学习笔记';syncFullscreen();
 progress(30,'加载数学资源','Loading mathematics');
})();
