// Single-finger gestures navigate the left reading sequence only. Native vertical
// scrolling, text selection, pinch zoom and all explicit controls remain native.
export function installReadingTouch({navigate}){
 const controls='button,a,input,select,textarea,summary,dialog,[role="button"],[contenteditable="true"],#diagramControls,.reading-rail';
 const localTap=`${controls},[data-formula],[data-concept],[data-p],.katex`;
 let gesture=null,suppressClickUntil=0;
 const horizontallyScrollable=target=>{
  for(let el=target;el&&el!==document.body;el=el.parentElement){
   if(el.scrollWidth>el.clientWidth+2&&/auto|scroll/.test(getComputedStyle(el).overflowX))return true;
  }
  return false;
 };
 document.addEventListener('touchstart',e=>{
  gesture=null;suppressClickUntil=0;
  if(e.touches.length!==1||document.querySelector('dialog[open]')||window.getSelection()?.toString())return;
  const target=e.target instanceof Element?e.target:e.target.parentElement;
  const control=target.closest(controls);
  const readingHeading=control?.matches('[data-select-build],[data-select-reading],[data-select-section],[data-formula]');
  if(!target.closest('.workspace,#mathLoader')||(control&&!readingHeading)||horizontallyScrollable(target))return;
  const touch=e.touches[0];
  // Leave the browser's own edge gestures available.
  if(touch.clientX<20||touch.clientX>innerWidth-20)return;
  gesture={id:touch.identifier,x:touch.clientX,y:touch.clientY,dx:0,dy:0,time:performance.now(),horizontal:false,tap:!target.closest(localTap)};
 },{passive:true});
 document.addEventListener('touchmove',e=>{
  if(!gesture)return;
  if(e.touches.length!==1){gesture=null;return;}
  const touch=Array.from(e.touches).find(t=>t.identifier===gesture.id);if(!touch)return;
  gesture.dx=touch.clientX-gesture.x;gesture.dy=touch.clientY-gesture.y;
  const x=Math.abs(gesture.dx),y=Math.abs(gesture.dy);
  if(!gesture.horizontal){
   if(y>10&&y>=x){gesture=null;return;}
   if(x>12&&x>1.5*y)gesture.horizontal=true;
  }
  if(gesture.horizontal){if(e.cancelable)e.preventDefault();else gesture=null;}
 },{passive:false});
 document.addEventListener('touchend',e=>{
  const g=gesture;gesture=null;if(!g||e.touches.length)return;
  const touch=Array.from(e.changedTouches).find(t=>t.identifier===g.id);if(!touch)return;
  const dx=touch.clientX-g.x,dy=touch.clientY-g.y,duration=performance.now()-g.time;
  const swipe=g.horizontal&&Math.abs(dx)>=56&&Math.abs(dx)>1.5*Math.abs(dy)&&duration<1600;
  const tap=g.tap&&!g.horizontal&&Math.hypot(dx,dy)<10&&duration<550;
  if((!swipe&&!tap)||window.getSelection()?.toString())return;
  // Consume the compatibility click so one touch cannot also activate a newly
  // revealed formula or button after the reading pane repositions its content.
  if(e.cancelable)e.preventDefault();suppressClickUntil=performance.now()+700;
  navigate(swipe&&dx<0?-1:1);
 },{passive:false});
 document.addEventListener('touchcancel',()=>{gesture=null;},{passive:true});
 document.addEventListener('click',e=>{
  if(e.isTrusted&&performance.now()<suppressClickUntil){e.preventDefault();e.stopImmediatePropagation();}
 },true);
}
