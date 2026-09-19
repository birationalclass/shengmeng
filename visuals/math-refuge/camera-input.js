// Local to Math Refuge: do not change the shared OrbitControls implementation.
export const DEFAULT_ROTATION=.22;
export function configureCameraInput(controls,element){
  let sensitivity=DEFAULT_ROTATION,pointerType='mouse';
  controls.enableDamping=true;controls.dampingFactor=.14;
  const apply=()=>{controls.rotateSpeed=sensitivity*(pointerType==='touch'?.75:1);};
  const pointer=event=>{pointerType=event.pointerType;apply();};
  // Capture runs before OrbitControls begins handling this pointer gesture.
  element.addEventListener('pointerdown',pointer,{capture:true,passive:true});apply();
  return {set(value){
    const number=Number(value);sensitivity=Number.isFinite(number)?Math.max(.08,Math.min(.6,number)):DEFAULT_ROTATION;apply();
  },dispose(){element.removeEventListener('pointerdown',pointer,true);}};
}
