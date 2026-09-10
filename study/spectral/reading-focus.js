// One reading position for every numbered entry, across section boundaries.
export function createReadingFocus({motion,column,mobilePane}) {
 const narrow=matchMedia('(max-width:780px)');
 let frame=0,current=null;
 const cancel=()=>{cancelAnimationFrame(frame);frame=0;};
 const layoutTop=el=>{let y=0;for(let node=el;node;node=node.offsetParent)y+=node.offsetTop;return y;};
 function follow(card){
  cancel();current=card;if(!card)return;
  const pane=narrow.matches?mobilePane:column;
  column.style.setProperty('--reading-tail-space',`${Math.round(pane.clientHeight*.78)}px`);
  const duration=motion.duration(),until=performance.now()+duration+350;
  let last=performance.now();
  const target=()=>{
   const height=pane.clientHeight,room=height-card.offsetHeight;
   // Keep context above a short entry; align a tall entry near the top.
   const inset=Math.max(12,Math.min(height*.22,room/2));
   const top=layoutTop(card)-layoutTop(pane)-inset;
   return Math.max(0,Math.min(top,pane.scrollHeight-height));
  };
  const step=now=>{
   if(!card.isConnected||card.hidden){cancel();return;}
   const goal=target(),distance=goal-pane.scrollTop;
   const dt=Math.min(40,Math.max(1,now-last));last=now;
   pane.scrollTop=duration?pane.scrollTop+distance*(1-Math.exp(-dt/70)):goal;
   if(duration&&(now<until||Math.abs(goal-pane.scrollTop)>1))frame=requestAnimationFrame(step);else frame=0;
  };
  if(duration)frame=requestAnimationFrame(step);else step(last);
 }
 for(const pane of new Set([column,mobilePane])){
  pane.addEventListener('wheel',cancel,{passive:true});pane.addEventListener('touchstart',cancel,{passive:true});
 }
 const resize=()=>{if(current?.isConnected&&!current.hidden){cancel();frame=requestAnimationFrame(()=>follow(current));}};
 window.addEventListener('resize',resize);narrow.addEventListener('change',resize);
 return {follow,cancel,isMoving:()=>!!frame};
}
