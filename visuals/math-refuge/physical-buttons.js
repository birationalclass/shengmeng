// A short, deliberate press activates a modeled button. Drag/cancel never do.
export function bindPhysicalButtons(canvas,controls,hitTest,activate){
  let press=null;
  function release(){if(!press)return;controls.enabled=press.enabled;press.object.userData.pressed=false;press=null;}
  function down(e){
    if(e.button!==0||press)return;const object=hitTest(e);if(!object)return;
    press={object,id:e.pointerId,x:e.clientX,y:e.clientY,enabled:controls.enabled};
    object.userData.pressed=true;controls.enabled=false;canvas.setPointerCapture?.(e.pointerId);e.preventDefault();e.stopImmediatePropagation();
  }
  function up(e){
    if(!press||press.id!==e.pointerId)return;
    const action=Math.hypot(e.clientX-press.x,e.clientY-press.y)<7&&hitTest(e)===press.object?press.object.userData.action:null;
    release();canvas.releasePointerCapture?.(e.pointerId);e.preventDefault();e.stopImmediatePropagation();if(action)activate(action);
  }
  function cancel(){release();}
  const events=[['pointerdown',down],['pointerup',up],['pointercancel',cancel],['lostpointercapture',cancel]];
  for(const [type,fn] of events)canvas.addEventListener(type,fn,true);
  return {dispose(){release();for(const [type,fn] of events)canvas.removeEventListener(type,fn,true);}};
}
