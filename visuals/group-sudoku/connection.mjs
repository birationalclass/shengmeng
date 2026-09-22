// One request chain at a time. Browsers' online events are hints; HTTP proves connectivity.
export function reconnectDelay(failures,random=Math.random){
 return Math.round(Math.min(60000,2000*2**Math.min(5,Math.max(0,failures-1)))*(.8+.2*random()));
}
export function createConnection({run,onState=()=>{},online=()=>navigator.onLine!==false,visible=()=>!document.hidden,random=Math.random,setTimer=setTimeout,clearTimer=clearTimeout}){
 let timer,controller,failures=0,stopped=false,again=false,state='connecting',generation=0;
 function emit(value){state=value;onState(value);}
 function schedule(delay){clearTimer(timer);timer=setTimer(tick,delay);}
 async function tick(){
  clearTimer(timer);timer=null;if(stopped||controller)return;
  if(!visible())return;
  if(!online()){emit('offline');schedule(60000);return;}
  const current=++generation;controller=new AbortController();
  if(state!=='connected')emit(failures?'retrying':'connecting');
  let next=60000;
  try{await run({signal:controller.signal});if(current!==generation)return;failures=0;emit('connected');}
  catch{if(current!==generation)return;failures++;emit(online()?'retrying':'offline');next=reconnectDelay(failures,random);}
  finally{if(current===generation){controller=null;if(!stopped&&visible()){schedule(again?0:next);again=false;}}}
 }
 function wake(){
  if(stopped)return;
  if(!visible()||!online()){generation++;controller?.abort();controller=null;again=false;clearTimer(timer);timer=null;if(!online())emit('offline');return;}
  if(controller){again=true;return;}schedule(0);
 }
 schedule(0);
 return {wake,pause(){generation++;clearTimer(timer);controller?.abort();controller=null;again=false;},get state(){return state;},stop(){stopped=true;generation++;clearTimer(timer);controller?.abort();controller=null;}};
}
