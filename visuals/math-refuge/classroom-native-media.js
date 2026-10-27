// The same native-media contract as the verified Refuge classroom controls:
// one element, a complete local PCM source, metadata/position first, rate last.
export function createClassroomNativeMedia(makeAudio=()=>new Audio()){
 let element=null,current=null,created=0,attachments=0;
 function detach(){current?.cancel();current=null;}
 function attach(url,{at=0}={}){
  detach();const audio=element||=(created++,makeAudio());audio.pause();
  const controller=new AbortController(),listeners=[];let resolveReady,settled=false;
  const lease={audio,signal:controller.signal,metadataReady:false,valid:()=>current===lease&&!controller.signal.aborted,cancel(){controller.abort();for(const [name,fn]of listeners)audio.removeEventListener(name,fn);listeners.length=0;if(!settled){settled=true;resolveReady(false);}}};
  current=lease;attachments++;lease.ready=new Promise(resolve=>resolveReady=resolve);
  const listen=(name,fn)=>{audio.addEventListener(name,fn);listeners.push([name,fn]);};
  const metadata=()=>{if(!lease.valid()||settled)return;audio.currentTime=Math.max(0,at);lease.metadataReady=true;settled=true;resolveReady(true);};
  listen('loadedmetadata',metadata);listen('error',()=>{if(!settled){settled=true;resolveReady(false);}});
  audio.preload='auto';audio.preservesPitch=true;audio.src=url;
  // load() resets the former resource's clock even when its position was nonzero.
  // Lightweight injected players in non-browser tests need no metadata wait.
  if(typeof audio.load==='function'&&typeof audio.readyState==='number')audio.load();else metadata();
  return lease;
 }
 function clear(){detach();if(element){element.pause();element.removeAttribute?.('src');element.load?.();}}
 function dispose(){clear();element=null;}
 return{attach,detach,clear,dispose,get state(){return{mode:'native-pcm',elementsCreated:created,attachments,metadataReady:Boolean(current?.metadataReady),active:Boolean(current?.valid())};}};
}
