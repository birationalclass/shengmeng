/* Keep the shared course/lesson toolbar quiet while the pointer is still. */
(()=>{
  'use strict';
  const header=document.querySelector('.portal-header');if(!header)return;
  const finePointer=matchMedia('(hover:hover) and (pointer:fine)');
  const phone=matchMedia('(max-width:767px), (pointer:coarse) and (max-width:1024px)');
  let timer=0;
  function wake(){
    clearTimeout(timer);header.classList.remove('is-idle');
    if(!finePointer.matches||phone.matches||document.hidden)return;
    timer=setTimeout(()=>{
      if(!document.querySelector('dialog[open]')&&!header.querySelector(':focus-visible'))header.classList.add('is-idle');
    },2400);
  }
  function listen(target){
    if(!target)return;
    for(const type of ['pointermove','pointerdown','keydown','focusin','focusout'])target.addEventListener(type,wake,{passive:true});
  }
  listen(document);
  const frame=document.getElementById('lecture-frame');
  // Pointer events inside the same-origin lesson iframe do not bubble to the portal.
  if(frame){frame.addEventListener('load',()=>{listen(frame.contentDocument);wake();});listen(frame.contentDocument);}
  document.addEventListener('close',wake,true);
  document.addEventListener('visibilitychange',wake);
  document.addEventListener('fullscreenchange',wake);
  window.addEventListener('course-language',wake);
  window.addEventListener('focus',wake);
  finePointer.addEventListener('change',wake);phone.addEventListener('change',wake);
  new MutationObserver(wake).observe(document.body,{attributes:true,attributeFilter:['class']});
  wake();
})();
