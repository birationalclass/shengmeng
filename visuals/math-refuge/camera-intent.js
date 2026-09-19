// Separate a fresh click from the compatibility click that can follow a drag.
// No pointer-up, inertia-end, focus or timer in this module can start a tour.
export function bindCameraIntent(root,canvas,onManual,now=()=>performance.now()){
  const pointers=new Map();let blockedUntil=-Infinity;
  const onCanvas=target=>target===canvas||canvas.contains?.(target);
  const relevant=target=>onCanvas(target)||Boolean(target?.closest?.('#chapters,#tour,#lectureButton,#lectureFocus'));
  function down(event){
    if(!relevant(event.target))return;
    if(pointers.size===0)blockedUntil=-Infinity; // a new, deliberate gesture
    const camera=Boolean(onCanvas(event.target));
    pointers.set(event.pointerId,{x:event.clientX,y:event.clientY,dragged:false,camera,type:event.pointerType});
    if(camera)onManual(); // capture phase, before OrbitControls changes the view
  }
  function move(event){
    const p=pointers.get(event.pointerId);if(!p)return;
    const threshold=p.type==='touch'?8:4;
    if(Math.hypot(event.clientX-p.x,event.clientY-p.y)>threshold){
      if(!p.dragged){p.dragged=true;onManual();}
      blockedUntil=now()+600;
    }
  }
  function up(event){
    move(event);const p=pointers.get(event.pointerId);
    if(p?.dragged)blockedUntil=now()+600;
    pointers.delete(event.pointerId);
  }
  function cancel(event){
    const p=pointers.get(event.pointerId);if(p?.camera||p?.dragged)onManual();
    pointers.delete(event.pointerId);blockedUntil=now()+600;
  }
  function canActivate(){return pointers.size===0&&now()>=blockedUntil;}
  function click(event){if(relevant(event.target)&&!canActivate()){event.preventDefault();event.stopImmediatePropagation();}}
  function abandon(){if(pointers.size){onManual();pointers.clear();blockedUntil=now()+600;}}
  const visibility=()=>{if(root.hidden)abandon();};
  const bindings=[['pointerdown',down],['pointermove',move],['pointerup',up],['pointercancel',cancel],['click',click]];
  for(const [name,fn] of bindings)root.addEventListener(name,fn,true);
  root.defaultView?.addEventListener('blur',abandon);root.addEventListener('visibilitychange',visibility);
  return {canActivate,hasPointers:()=>pointers.size>0,dispose(){for(const [name,fn] of bindings)root.removeEventListener(name,fn,true);root.defaultView?.removeEventListener('blur',abandon);root.removeEventListener('visibilitychange',visibility);pointers.clear();}};
}
