// One output graph per page. Keep native preservesPitch while avoiding cold sinks.
let context=null,bus=null,warmed=false,warmJob=null,contextsCreated=0,connections=0;
const sources=new WeakMap();
function outputContext(){
 const Context=globalThis.AudioContext||globalThis.webkitAudioContext;
 if(!Context)return null;
 if(!context||context.state==='closed'){
  context=new Context({latencyHint:'interactive'});contextsCreated++;warmed=false;
  bus=context.createGain();bus.gain.value=1;bus.connect(context.destination);
 }
 return context;
}
export async function primeClassroomAudio(audio){
 if(typeof globalThis.HTMLMediaElement==='undefined'||!(audio instanceof HTMLMediaElement))return false;
 const ctx=outputContext();if(!ctx)return false;
 if(ctx.state!=='running'){
  warmed=false;
  await Promise.race([ctx.resume(),new Promise(resolve=>setTimeout(resolve,600))]);
 }
 if(ctx.state!=='running'){
  if(sources.has(audio))throw Error('请再次点击播放以启用音频输出');
  return false; // Keep the native audio path if the Web Audio unlock was blocked.
 }
 if(audio.readyState<HTMLMediaElement.HAVE_ENOUGH_DATA){
  await new Promise((resolve,reject)=>{
   const finish=error=>{clearTimeout(timer);audio.removeEventListener('canplaythrough',ready);audio.removeEventListener('error',failed);error?reject(error):resolve();};
   const ready=()=>finish(),failed=()=>finish(Error('语音尚未解码完成，请重试'));
   const timer=setTimeout(()=>finish(Error('语音准备超时，请重试')),15000);
   audio.addEventListener('canplaythrough',ready,{once:true});audio.addEventListener('error',failed,{once:true});
  });
 }
 let item=sources.get(audio);
 if(!item){item={node:ctx.createMediaElementSource(audio),connected:false};sources.set(audio,item);}
 if(!item.connected){item.node.connect(bus);item.connected=true;connections++;}
 audio.preservesPitch=true;
 if(!warmed){
  if(!warmJob)warmJob=(async()=>{
   const silent=ctx.createBufferSource();silent.buffer=ctx.createBuffer(1,Math.ceil(ctx.sampleRate*.22),ctx.sampleRate);
   silent.connect(bus);silent.start();await new Promise(resolve=>setTimeout(resolve,240));silent.disconnect();warmed=true;
  })().finally(()=>{warmJob=null;});
  await warmJob;
 }
 return true;
}
export function disconnectClassroomAudio(audio){
 const item=audio&&sources.get(audio);if(item?.connected){item.node.disconnect();item.connected=false;connections--;}
}
export function classroomAudioOutputState(){return{contextState:context?.state||'not-created',contextsCreated,warmed,connections};}
