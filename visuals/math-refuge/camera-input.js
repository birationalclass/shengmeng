// Local to Math Refuge: do not change the shared OrbitControls implementation.
export const DEFAULT_ROTATION=.22;
export function configureCameraInput(controls,element){
  let sensitivity=DEFAULT_ROTATION,pointerType='mouse';
  controls.enableDamping=true;controls.dampingFactor=.14;
  const apply=()=>{controls.rotateSpeed=sensitivity*(pointerType==='touch'?.75:1);};
  const leftButton=controls.mouseButtons?.LEFT;if(controls.mouseButtons)controls.mouseButtons.LEFT=null;let drag=null;
  const down=e=>{if(e.button!==0||e.pointerType==='touch'||!controls.enabled)return;drag={id:e.pointerId,x:e.clientX,y:e.clientY,at:e.timeStamp,moved:false};element.setPointerCapture?.(e.pointerId);};
  const move=e=>{if(!drag||drag.id!==e.pointerId||!controls.enabled)return;const dx=e.clientX-drag.x,dy=e.clientY-drag.y;if(!drag.moved&&Math.hypot(dx,dy)<4)return;if(!drag.moved){drag.moved=true;controls.dispatchEvent({type:'start'});}const elapsed=Math.max(1/240,Math.min(.05,(e.timeStamp-drag.at)/1000||1/60));drag.at=e.timeStamp;drag.x=e.clientX;drag.y=e.clientY;e.preventDefault();e.stopImmediatePropagation();
    const position=controls.object.position.clone(),direction=controls.target.clone().sub(position),length=Math.max(.4,direction.length()),yaw=Math.atan2(direction.x,direction.z)+Math.max(-1.8*elapsed,Math.min(1.8*elapsed,-dx*sensitivity*.012)),pitch=Math.max(-1.45,Math.min(1.45,Math.asin(direction.y/length)+Math.max(-1.8*elapsed,Math.min(1.8*elapsed,dy*sensitivity*.009))));
    direction.set(Math.sin(yaw)*Math.cos(pitch)*length,Math.sin(pitch)*length,Math.cos(yaw)*Math.cos(pitch)*length);controls.target.copy(position).add(direction);const damping=controls.enableDamping;controls.enableDamping=false;controls.update();controls.enableDamping=damping;controls.object.position.copy(position);
  };
  const up=e=>{if(!drag||drag.id!==e.pointerId)return;const moved=drag.moved;drag=null;if(element.hasPointerCapture?.(e.pointerId))element.releasePointerCapture(e.pointerId);if(moved)controls.dispatchEvent({type:'end'});};
  for(const [type,fn] of [['pointerdown',down],['pointermove',move],['pointerup',up],['pointercancel',up]])element.addEventListener(type,fn,true);
  const pointer=event=>{pointerType=event.pointerType;apply();};
  // Capture runs before OrbitControls begins handling this pointer gesture.
  element.addEventListener('pointerdown',pointer,{capture:true,passive:true});apply();
  const wheel=event=>{if(!controls.enabled||!controls.object)return;event.preventDefault();event.stopImmediatePropagation();
    const direction=controls.target.clone().sub(controls.object.position).normalize();
    const pixels=event.deltaY*(event.deltaMode===1?16:event.deltaMode===2?element.clientHeight:1);
    direction.multiplyScalar(-Math.max(-240,Math.min(240,pixels))*.012);
    controls.object.position.add(direction);controls.target.add(direction);controls.update();
    controls.dispatchEvent({type:'start'});controls.dispatchEvent({type:'end'});
  };
  element.addEventListener('wheel',wheel,{capture:true,passive:false});
  return {set(value){
    const number=Number(value);sensitivity=Number.isFinite(number)?Math.max(.08,Math.min(.6,number)):DEFAULT_ROTATION;apply();
  },dispose(){if(controls.mouseButtons)controls.mouseButtons.LEFT=leftButton;for(const [type,fn] of [['pointerdown',down],['pointermove',move],['pointerup',up],['pointercancel',up]])element.removeEventListener(type,fn,true);element.removeEventListener('pointerdown',pointer,true);element.removeEventListener('wheel',wheel,true);}};
}
