// Phones keep the normal cover. Only Start reading creates a landscape viewport.
// The same-origin frame gives SVG, HTML mathematics, media queries and pointer
// coordinates one real viewport; individual diagram layers are never rotated.
(()=>{
 const mode='reading-frame';
 let owner=null;
 try{if(window.parent!==window&&new URL(location.href).searchParams.get(mode)==='landscape'&&window.frameElement?.id==='mobileReadingFrame'&&window.parent.spectralMobileReading)owner=window.parent.spectralMobileReading;}catch{}
 const isFrame=!!owner,english=()=>localStorage.getItem('spectral-language')==='en';
 if(isFrame)document.documentElement.dataset.mobileReading='landscape';
 const phone=()=>!isFrame&&matchMedia('(any-pointer:coarse)').matches&&Math.min(screen.width,screen.height,innerWidth,innerHeight)<=600;
 const start=()=>document.getElementById('beginSlides');
 let host=null,frame=null,ready=false,active=false,timer=0,resizeFrame=0,lockHeld=false;
 function size(){
  if(!host)return;
  const w=host.clientWidth,h=host.clientHeight,portrait=h>w,long=Math.max(w,h),short=Math.min(w,h);
  const width=Math.max(800,long),scale=long/width,height=short/scale;
  frame.style.width=`${width}px`;frame.style.height=`${height}px`;
  frame.style.transform=`translate(-50%,-50%) rotate(${portrait?90:0}deg) scale(${scale})`;
  host.dataset.orientation=portrait?'rotated':'landscape';
 }
 const resize=()=>{cancelAnimationFrame(resizeFrame);resizeFrame=requestAnimationFrame(size);};
 function sync(){
  const hint=document.getElementById('mobileReadingHint');if(hint){hint.hidden=!phone();hint.querySelector('strong').textContent=english()?'Landscape reading on phones':'手机仅支持横屏阅读';hint.querySelector('span').textContent=english()?'The layout rotates when you start.':'点击开始阅读后，自动切换为横向布局。';}
  if(frame){frame.title=english()?'Spectral Sequence · landscape reading':'谱序列 · 横屏阅读';if(!ready){start().disabled=true;start().textContent=english()?'Opening…':'正在进入…';start().setAttribute('aria-busy','true');}}
 }
 function dispose(){
  clearTimeout(timer);cancelAnimationFrame(resizeFrame);host?.remove();host=frame=null;ready=active=false;
  document.body.classList.remove('mobile-reading-active');
  document.querySelectorAll('body > header,body > main,body > footer').forEach(el=>el.inert=false);
  start().removeAttribute('aria-busy');
 }
 function requestEntry(){
  if(isFrame||!phone()||ready)return false;
  if(frame)return true;
  host=document.createElement('div');host.id='mobileReadingHost';
  frame=document.createElement('iframe');frame.id='mobileReadingFrame';frame.setAttribute('allow','fullscreen');frame.setAttribute('allowfullscreen','');
  const url=new URL(location.href);url.searchParams.set(mode,'landscape');url.hash='title';frame.src=url.href;
  host.append(frame);document.body.append(host);size();sync();
  timer=setTimeout(()=>failed(frame?.contentWindow),20000);
  return true;
 }
 function loaded(child){
  if(!frame||frame.contentWindow!==child)return;
  clearTimeout(timer);ready=true;active=true;size();
  start().disabled=false;start().removeAttribute('aria-busy');start().click();
  document.body.classList.add('mobile-reading-active');
  document.querySelectorAll('body > header,body > main,body > footer').forEach(el=>el.inert=true);
  host.classList.add('is-ready');syncFullscreen(document.body.classList.contains('study-fullscreen'));
  frame.focus({preventScroll:true});child.focus();
 }
 function failed(child){
  if(!frame||frame.contentWindow!==child)return;
  dispose();start().disabled=false;start().textContent=english()?'Retry opening':'重新进入';
 }
 function cover(child){
  if(!frame||frame.contentWindow!==child)return;
  // Language changes inside the reader persist when returning to the outer cover.
  const wanted=english()?'en':'zh';
  dispose();
  if(window.spectralState?.language!==wanted)document.getElementById('languageButton').click();
  document.getElementById('coverButton').click();
 }
 function onReady(){
  if(!isFrame)return;
  requestAnimationFrame(()=>{start().click();requestAnimationFrame(()=>owner.loaded(window));});
 }
 // Cover is invoked after the app has reset its state, so test whether the parent
 // has already activated this child instead of relying on the child's cover flag.
 function returnToCover(){if(isFrame&&owner.active()){owner.cover(window);return true;}return false;}
 function syncFullscreen(value){if(frame&&ready)frame.contentWindow.spectralMobileReading?.receiveFullscreen(value);}
 function receiveFullscreen(value){if(!isFrame)return;document.body.classList.toggle('study-fullscreen',value);window.spectralFullscreen?.sync();}
 async function lockLandscape(){
  if(!active||!phone()||!document.fullscreenElement||!screen.orientation?.lock)return;
  try{await screen.orientation.lock('landscape');lockHeld=true;}catch{/* The landscape viewport is the fallback, including Safari. */}
 }
 function unlock(){if(lockHeld){try{screen.orientation.unlock();}catch{}lockHeld=false;}}
 window.spectralMobileReading={isFrame,active:()=>active,requestEntry,onReady,onFailure:()=>{if(isFrame)owner.failed(window);},sync,loaded,failed,cover,returnToCover,syncFullscreen,receiveFullscreen,lockLandscape,unlock,
  toggleFullscreen:()=>isFrame?window.parent.spectralFullscreen?.toggle():null,
  navigate:direction=>{if(active&&frame)frame.contentWindow.spectralNavigateReading?.(direction);}
 };
 window.addEventListener('resize',resize);window.visualViewport?.addEventListener('resize',resize);
 if(isFrame){
  // Mirror only the location, without exposing the internal frame query parameter.
  const notify=()=>requestAnimationFrame(()=>{try{const url=new URL(window.parent.location.href);url.hash=location.hash;window.parent.history.replaceState(null,'',url.href);}catch{}});
  document.addEventListener('click',notify);document.addEventListener('keydown',notify);
 }
 sync();
})();
