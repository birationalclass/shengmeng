// Brightness depends only on whether the pointer is in a toolbar region.
(()=>{
 const fine=matchMedia('(hover:hover) and (pointer:fine)');
 const regions=[...document.querySelectorAll('.notebook-toolbar,.cover-actions')];
 const active=new Set();
 const sync=()=>document.body.classList.toggle('toolbar-idle',fine.matches&&active.size===0);
 for(const region of regions){
  region.addEventListener('pointerenter',()=>{active.add(region);sync();},{passive:true});
  region.addEventListener('pointerleave',()=>{active.delete(region);sync();},{passive:true});
  region.addEventListener('pointercancel',()=>{active.delete(region);sync();},{passive:true});
 }
 fine.addEventListener('change',sync);window.addEventListener('blur',()=>{active.clear();sync();});sync();
})();
