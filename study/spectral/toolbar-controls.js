// Shared pacing with the abstract-algebra lesson, without moving hit targets.
(()=>{
 const fine=matchMedia('(hover:hover) and (pointer:fine)');
 let timer=0;
 function wake(){
  clearTimeout(timer);document.body.classList.remove('toolbar-idle');
  if(!fine.matches||document.hidden)return;
  timer=setTimeout(()=>{
   if(!document.querySelector('dialog[open],.notebook-toolbar :focus-visible,.cover-actions :focus-visible'))document.body.classList.add('toolbar-idle');
  },2400);
 }
 for(const type of ['pointermove','pointerdown','keydown','focusin','focusout'])document.addEventListener(type,wake,{passive:true});
 document.addEventListener('close',wake,true);
 document.addEventListener('visibilitychange',wake);
 document.addEventListener('fullscreenchange',wake);
 window.addEventListener('focus',wake);
 fine.addEventListener('change',wake);
 // Dialogs remain bright; closing them rearms the quiet timer.
 new MutationObserver(wake).observe(document.body,{subtree:true,attributes:true,attributeFilter:['open']});
 wake();
})();
