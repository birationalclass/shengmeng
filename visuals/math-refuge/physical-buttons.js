// A short, deliberate press activates a modeled button. Drag/cancel never do.
export function bindPhysicalButtons(canvas,controls,hitTest,activate){
  let press=null,hover=null;const cursor=canvas.style?.cursor||'';
  function highlight(object){
    if(hover===object)return;
    if(hover)hover.userData.hovered=false;hover=object;
    if(hover)hover.userData.hovered=true;
    if(canvas.style)canvas.style.cursor=hover?.userData.action||hover?.userData.autoDoor?'pointer':cursor;
  }
  function move(e){highlight(press||e.buttons?null:hitTest(e));}
  function leave(){highlight(null);}
  function release(){if(!press)return;controls.enabled=press.enabled;press.object.userData.pressed=false;press=null;}
  function down(e){
    if(e.button!==0||press)return;const object=hitTest(e);if(!object?.userData.action)return;highlight(object);
    press={object,id:e.pointerId,x:e.clientX,y:e.clientY,enabled:controls.enabled};
    object.userData.pressed=true;controls.enabled=false;canvas.setPointerCapture?.(e.pointerId);e.preventDefault();e.stopImmediatePropagation();
  }
  function up(e){
    if(!press||press.id!==e.pointerId)return;
    const action=Math.hypot(e.clientX-press.x,e.clientY-press.y)<7&&hitTest(e)===press.object?press.object.userData.action:null;
    release();canvas.releasePointerCapture?.(e.pointerId);e.preventDefault();e.stopImmediatePropagation();if(action)activate(action);
  }
  function cancel(){release();highlight(null);}
  const events=[['pointerdown',down],['pointerup',up],['pointermove',move],['pointerleave',leave],['pointercancel',cancel],['lostpointercapture',cancel]];
  for(const [type,fn] of events)canvas.addEventListener(type,fn,true);
  return {dispose(){release();highlight(null);for(const [type,fn] of events)canvas.removeEventListener(type,fn,true);}};
}
