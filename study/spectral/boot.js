// One cover for loading and entry. Typesetting never advances into the lesson.
(()=>{
 const overlay=document.getElementById('mathLoader'),status=document.getElementById('loaderStatus'),bar=overlay.querySelector('[role=progressbar]'),start=document.getElementById('beginSlides');
 let done=false,failed=false,progressValue=0,progressLabels=['加载数学资源','Loading mathematics'];
 const en=()=>localStorage.getItem('spectral-language')==='en';
 let stopTitleEntrance=()=>{},coverLanguage=null,entranceRequest=0;
 let coverFont='c';try{const saved=localStorage.getItem('spectral-cover-font');if(['a','c'].includes(saved))coverFont=saved;}catch{}
 overlay.dataset.coverFont=coverFont;
 window.spectralCover={style:()=>coverFont,setStyle:value=>{
  if(!['a','c'].includes(value)||value===coverFont)return;
  coverFont=value;overlay.dataset.coverFont=value;try{localStorage.setItem('spectral-cover-font',value);}catch{}
  if(!en()&&!overlay.hidden&&!overlay.classList.contains('is-ready'))animateTitle();
 }};
 // Animate measured glyph positions on entry and language changes; keep the accessible title intact.
 const animateTitle=async()=>{
  const request=++entranceRequest;stopTitleEntrance();
  const title=overlay.querySelector('.loader-title'),face=title.querySelector(':scope > .loader-title-face');
  if(!face||matchMedia('(prefers-reduced-motion:reduce)').matches||!Element.prototype.animate)return;
  overlay.classList.add('cover-intro');title.classList.add('is-assembling');
  if(coverFont==='c'&&title.lang==='zh-CN'){
   try{await document.fonts.load('96px "Cover Ma Shan Zheng"','谱序列');}catch{}
   if(request!==entranceRequest)return;
  }
  const bounds=title.getBoundingClientRect(),faceBounds=face.getBoundingClientRect(),text=face.firstChild;
  const letters=[];let offset=0;
  for(const glyph of Array.from(text.textContent)){
   const range=document.createRange();range.setStart(text,offset);offset+=glyph.length;range.setEnd(text,offset);
   const rect=range.getBoundingClientRect();if(!glyph.trim())continue;
   const letter=document.createElement('span');letter.className='loader-title-letter';letter.setAttribute('aria-hidden','true');
   letter.style.left=`${rect.left-bounds.left}px`;letter.style.top=`${faceBounds.top-bounds.top}px`;
   for(const name of ['loader-title-depth','loader-title-face']){const layer=document.createElement('span');layer.className=name;layer.textContent=glyph;letter.append(layer);}
   letters.push(letter);
  }
  overlay.classList.add('cover-intro');title.classList.add('is-assembling');title.append(...letters);
  let settled=false;
  const finish=()=>{if(settled)return;settled=true;stopTitleEntrance=()=>{};letters.forEach(letter=>letter.remove());title.classList.remove('is-assembling');overlay.classList.remove('cover-intro');window.removeEventListener('resize',cancel);};
  const animations=letters.map(letter=>{
   const distance=(Math.random()<.5?-1:1)*(55+Math.random()*Math.min(170,innerHeight*.2));
   return letter.animate([{transform:`translateY(${distance}px)`,opacity:0},{transform:'translateY(0)',opacity:1}],
    {duration:1300+Math.random()*500,delay:Math.random()*320,easing:'cubic-bezier(.16,1,.3,1)',fill:'both'});
  });
  // A resize/fullscreen transition must immediately restore the responsive title.
  const cancel=()=>{animations.forEach(animation=>animation.cancel());finish();};
  stopTitleEntrance=cancel;
  window.addEventListener('resize',cancel,{once:true});
  Promise.all(animations.map(animation=>animation.finished)).then(finish,finish);
 };

 const coverFullscreen=document.getElementById('coverFullscreen'),lessonFullscreen=document.getElementById('fullscreen');
 let fullscreenScroll=0,fullscreenPending=false;
 const fullscreenActive=()=>document.body.classList.contains('study-fullscreen');
 const syncFullscreen=()=>{
  document.title=en()?'Spectral Sequence · Sheng Meng':'谱序列 · 孟晟';
  document.querySelector('.toolbar-actions').setAttribute('aria-label',en()?'Spectral Sequence':'谱序列');
  const active=fullscreenActive(),label=en()?(active?'Exit Full':'Full'):(active?'退出全屏':'全屏'),actionLabel=en()?(active?'Exit fullscreen':'Enter fullscreen'):(active?'退出全屏':'进入全屏');
  coverFullscreen.querySelector('span').textContent=label;lessonFullscreen.textContent='⛶ '+label;
  for(const button of [coverFullscreen,lessonFullscreen]){button.setAttribute('aria-pressed',String(active));button.setAttribute('aria-label',actionLabel);button.title=active?actionLabel+' (Esc)':actionLabel;button.disabled=fullscreenPending;}
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
 const progress=(value,zh,english)=>{if(done||failed)return;progressLabels=[zh,english];progressValue=Math.max(progressValue,Math.min(100,Math.max(0,value)));bar.setAttribute('aria-valuenow',progressValue);bar.firstElementChild.style.transform=`scaleX(${progressValue/100})`;status.textContent=en()?english:zh;};
 const fail=()=>{if(done)return;failed=true;overlay.classList.add('loading-failed');status.textContent=en()?'Unable to load mathematics':'数学资源加载失败';document.getElementById('loaderRetry').hidden=false;};
 const syncCoverLanguage=()=>{
  const english=en(),button=document.getElementById('coverLanguage');
  const replay=coverLanguage!==null&&coverLanguage!==english;coverLanguage=english;
  const title=overlay.querySelector('.loader-title'),face=title.querySelector(':scope > .loader-title-face');
  const titleText=english?'Spectral Sequence':'谱序列',author=overlay.querySelector('.loader-author');
  if(face.textContent!==titleText){stopTitleEntrance();face.textContent=titleText;title.querySelector(':scope > .loader-title-depth').textContent=titleText;}
  title.lang=author.lang=english?'en':'zh-CN';author.textContent=english?'Sheng Meng':'孟晟';
  overlay.querySelector('.loader-eyebrow').textContent=english?'Study Notes':'学习笔记';
  button.textContent=english?'中文':'Eng';button.lang=english?'zh-CN':'en';
  button.setAttribute('aria-label',english?'切换为中文':'Switch to English');
  const settingsButton=document.getElementById('coverSettings');settingsButton.querySelector('span').textContent=english?'Settings':'设置';settingsButton.setAttribute('aria-label',english?'Display settings':'显示设置');
  start.textContent=english?'Start reading':'开始阅读';
  document.getElementById('loaderRetry').textContent=english?'Reload':'重新加载';
  bar.setAttribute('aria-label',english?'Loading mathematics':'加载数学资源');
  if(failed)status.textContent=english?'Unable to load mathematics':'数学资源加载失败';
  else if(!done)status.textContent=progressLabels[english?1:0];
  syncFullscreen();
  if(replay&&!overlay.hidden&&!overlay.classList.contains('is-ready'))animateTitle();
 };
 const showCover=()=>{
  overlay.hidden=false;overlay.classList.remove('is-ready');document.documentElement.classList.add('math-loading');
  syncCoverLanguage();
  if(done){start.disabled=false;start.hidden=false;status.textContent='';status.setAttribute('aria-hidden','true');}
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
 syncCoverLanguage();
 animateTitle();
 progress(30,'加载数学资源','Loading mathematics');
})();
