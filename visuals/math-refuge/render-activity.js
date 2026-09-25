// One owner for the render loop: visibility alone does not detect another app
// or window taking focus. A queued callback must obey the same gate as events.
export function bindRenderActivity({doc=document,win=window,setLoop,frame,onPause=()=>{},onResume=()=>{},now=()=>performance.now()}){
 let enabled=false,running=false,pageVisible=true,focused=doc.hasFocus(),pausedAt=null,disposed=false,inFrame=false;
 const foreground=()=>pageVisible&&!doc.hidden&&focused&&doc.hasFocus();
 const callback=stamp=>{inFrame=true;try{if(!foreground()){sync();return;}if(running)frame(stamp);}finally{inFrame=false;}};
 function sync(){
  const next=!disposed&&enabled&&foreground();
  if(next===running)return;
  running=next;
  if(next){const gap=pausedAt===null?0:Math.max(0,now()-pausedAt);pausedAt=null;onResume(gap);setLoop(callback);}
  else{pausedAt=now();setLoop(null);onPause();
   // Three schedules its next RAF after returning from the frame callback.
   // Cancel that too if suspension/error happened inside the callback itself.
   if(inFrame)queueMicrotask(()=>{if(!running)setLoop(null);});
  }
 }
 const listeners=[
  [win,'blur',()=>{focused=false;sync();}],
  [win,'focus',()=>{focused=true;sync();}],
  [doc,'visibilitychange',()=>{focused=doc.hasFocus();sync();}],
  [win,'pagehide',()=>{pageVisible=false;sync();}],
  [win,'pageshow',()=>{pageVisible=true;focused=doc.hasFocus();sync();}],
 ];
 for(const [target,event,handler] of listeners)target.addEventListener(event,handler);
 return {get running(){return running;},get foreground(){return foreground();},
  setEnabled(value){enabled=Boolean(value);sync();},
  dispose(){disposed=true;sync();for(const [target,event,handler] of listeners)target.removeEventListener(event,handler);},
 };
}
