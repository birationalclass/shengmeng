// Match the original standard rendering density; frame budgeting never reduces clarity.
export const MOBILE_PIXEL_RATIO=1.5;
export function domainAnimationActive(index,{mobile,fullscreen,touring,selected,sequence}){return !mobile||!!fullscreen||!!touring||selected===index||(sequence?.kind==='bridge'&&[sequence.index,sequence.index+1].includes(index));}
export function mobileDevice(width,height,coarse=false){return width<=600||(Math.min(width,height)<=600&&Math.max(width,height)<=1100)||(coarse&&Math.min(width,height)<=900);}
export function mobileFrameRate({moving=false,recent=false}={}){return moving||recent?30:15;}
export function gentleZoom(radius,ratio){
 const factor=Math.exp(Math.max(-.07,Math.min(.07,-Math.log(Math.max(.1,ratio))*.28)));
 // Same usable range as desktop; only gesture sensitivity is reduced.
 return Math.max(15,Math.min(230,radius*factor));
}
// Padding is a fraction of viewport height, so shallow landscape screens pull back.
export function mobileFrameScale(width,height){
 const top=height<500?48:85,bottom=height<500?65:180;
 const available=Math.max(height*.40,height-top-bottom);
 return Math.max(1.18,Math.min(2.8,height/available*.93),.98/(width/height));
}
export function bindPinch(element,{enabled,zoom,onStart=()=>{},onEnd=()=>{}}){
 let distance=0,active=false,suppressUntil=0;
 const gap=touches=>Math.hypot(touches[0].clientX-touches[1].clientX,touches[0].clientY-touches[1].clientY);
 element.addEventListener('touchstart',e=>{if(!enabled()||e.touches.length!==2)return;active=true;distance=gap(e.touches);suppressUntil=Date.now()+500;e.preventDefault();onStart();},{passive:false});
 element.addEventListener('touchmove',e=>{if(!active||e.touches.length!==2)return;e.preventDefault();const next=gap(e.touches);if(distance>0&&next>0)zoom(next/distance);distance=next;},{passive:false});
 const end=e=>{if(!active)return;e.preventDefault();if(e.touches.length<2){active=false;distance=0;suppressUntil=Date.now()+400;onEnd();}};
 element.addEventListener('touchend',end,{passive:false});element.addEventListener('touchcancel',end,{passive:false});
 element.addEventListener('click',e=>{if(active||Date.now()<suppressUntil){e.preventDefault();e.stopImmediatePropagation();}},true);
 return {get active(){return active;}};
}
