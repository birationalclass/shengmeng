// Only the toolbar's own interaction region can wake its controls.
(()=>{
 const fine=matchMedia('(hover:hover) and (pointer:fine)');
 const regions=[...document.querySelectorAll('.notebook-toolbar,.cover-actions')];
 let timer=0;
 const keyboardInside=()=>document.body.classList.contains('toolbar-keyboard')&&regions.some(r=>r.contains(document.activeElement));
 function arm(){clearTimeout(timer);if(!fine.matches){document.body.classList.remove('toolbar-idle');return;}timer=setTimeout(()=>{if(!keyboardInside())document.body.classList.add('toolbar-idle');},2400);}
 function wake(){document.body.classList.remove('toolbar-idle');arm();}
 for(const region of regions){
  for(const type of ['pointerenter','pointermove','pointerdown'])region.addEventListener(type,wake,{passive:true});
  region.addEventListener('pointerleave',arm,{passive:true});
  region.addEventListener('focusin',()=>{if(document.body.classList.contains('toolbar-keyboard'))wake();});
  region.addEventListener('focusout',arm);
 }
 document.addEventListener('pointerdown',()=>document.body.classList.remove('toolbar-keyboard'),{passive:true});
 document.addEventListener('keydown',()=>document.body.classList.add('toolbar-keyboard'),{passive:true});
 fine.addEventListener('change',arm);arm();
})();
