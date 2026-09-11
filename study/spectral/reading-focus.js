// One reading position for every numbered entry, across section boundaries.
export function createReadingFocus({motion,column,mobilePane}) {
 const narrow=matchMedia('(max-width:780px)'),toolbar=document.querySelector('.notebook-toolbar');
 let frame=0,current=null,tracking=false,pane=null,position=0,last=0,until=0;
 const cancel=()=>{cancelAnimationFrame(frame);frame=0;tracking=false;};
 const visible=()=>current?.isConnected&&!current.closest('[hidden]');
 // Layout coordinates ignore the frame's entrance scale. Include parent borders
 // so nested entries in section 2 use the same origin as entries in section 1.
 const layoutTop=el=>{let y=0;for(let node=el;node;node=node.offsetParent)y+=node.offsetTop+(node.offsetParent?.clientTop||0);return y;};
 function target(){
  const bounds=pane.getBoundingClientRect(),outer=mobilePane.getBoundingClientRect();
  const view=window.visualViewport,screenTop=view?.offsetTop||0,screenHeight=view?.height||innerHeight;
  const top=Math.max(screenTop,bounds.top+pane.clientTop,outer.top,toolbar?.getBoundingClientRect().bottom||0);
  const bottom=Math.min(screenTop+screenHeight,bounds.top+pane.clientTop+pane.clientHeight,outer.bottom);
  const gap=Math.min(16,Math.max(0,(bottom-top)/10));
  const middle=screenTop+screenHeight/2;
  // Prefer the screen midpoint. Move up only as far as the bottom requires;
  // oversized entries start below the toolbar and remain manually scrollable.
  const preferred=Math.max(top+gap,Math.min(middle,bottom-gap-current.offsetHeight));
  // Trailing room permits the last short entry to reach the midpoint. No leading
  // spacer is added: too little preceding content naturally clamps scroll to 0.
  const tail=Math.ceil(Math.max(0,pane.clientHeight-(middle-bounds.top)));
  const tailValue=`${tail}px`;
  if(column.style.getPropertyValue('--reading-tail-space')!==tailValue)column.style.setProperty('--reading-tail-space',tailValue);
  const wanted=layoutTop(current)-layoutTop(pane)-(preferred-bounds.top);
  return Math.max(0,Math.min(wanted,pane.scrollHeight-pane.clientHeight));
 }
 function step(now){
  frame=0;if(!tracking||!visible())return;
  const duration=motion.duration(),goal=target();
  const dt=Math.min(40,Math.max(1,now-last));last=now;
  const easingTime=Math.max(100,Math.min(220,duration*.18));
  // Keep the fractional position even when a browser rounds scrollTop. This
  // avoids both a stalled final pixel and a hard snap at the animation deadline.
  position=duration?position+(goal-position)*(1-Math.exp(-dt/easingTime)):goal;
  if(Math.abs(goal-position)<.15)position=goal;
  pane.scrollTop=position;
  if(duration&&(now<until||Math.abs(goal-position)>.15))frame=requestAnimationFrame(step);
 }
 function schedule(settleFor=240){
  if(!tracking||!visible())return;
  const nextPane=narrow.matches?mobilePane:column;
  if(nextPane!==pane){pane=nextPane;position=pane.scrollTop;}
  until=Math.max(until,performance.now()+settleFor);
  if(!frame){position=pane.scrollTop;last=performance.now();frame=requestAnimationFrame(step);}
 }
 function follow(card){
  cancel();if(current)cardObserver.unobserve(current);current=card;if(!visible())return;cardObserver.observe(current);
  pane=narrow.matches?mobilePane:column;tracking=true;position=pane.scrollTop;
  last=performance.now();until=last+motion.duration()+300;
  if(motion.duration())frame=requestAnimationFrame(step);else step(last);
 }
 // Explicit scrolling takes ownership until another entry is selected.
 for(const scrollport of new Set([column,mobilePane])){
  scrollport.addEventListener('wheel',cancel,{passive:true});
  scrollport.addEventListener('touchstart',cancel,{passive:true});
 }
 // Re-evaluate after folds, typography changes, fullscreen and viewport changes.
 // Observers wake the same follower; they never create a second scroll animation.
 const resize=()=>schedule();
 const cardObserver=new ResizeObserver(resize);
 new ResizeObserver(resize).observe(column.querySelector('#explanation'));
 const paneObserver=new ResizeObserver(resize);paneObserver.observe(column);paneObserver.observe(mobilePane);
 window.addEventListener('resize',resize);narrow.addEventListener('change',resize);
 window.visualViewport?.addEventListener('resize',resize);
 return {follow,cancel,isMoving:()=>!!frame};
}
