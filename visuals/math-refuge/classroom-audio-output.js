// Offline-decoded PCM uses the native media path from the successful controls.
// Do not route it through a live AudioContext or claim silent warmup proves onset.
const prepared=new WeakSet();let preparations=0;
export async function primeClassroomAudio(audio,{signal}={}){
 const aborted=()=>signal?.reason||new DOMException('Audio source replaced','AbortError');
 if(signal?.aborted)throw aborted();
 if(typeof globalThis.HTMLMediaElement==='undefined'||!(audio instanceof HTMLMediaElement))return false;
 if(audio.error)throw Error('语音解码失败，请重试');
 if(audio.readyState<HTMLMediaElement.HAVE_ENOUGH_DATA){
  await new Promise((resolve,reject)=>{
   const finish=error=>{clearTimeout(timer);audio.removeEventListener('canplaythrough',ready);audio.removeEventListener('error',failed);signal?.removeEventListener('abort',cancel);error?reject(error):resolve();};
   const ready=()=>finish(),failed=()=>finish(Error('语音尚未解码完成，请重试'));
    const cancel=()=>finish(aborted());
   const timer=setTimeout(()=>finish(Error('语音准备超时，请重试')),15000);
   audio.addEventListener('canplaythrough',ready,{once:true});audio.addEventListener('error',failed,{once:true});
    signal?.addEventListener('abort',cancel,{once:true});
  });
 }
 if(signal?.aborted)throw aborted();
 audio.preservesPitch=true;
 if(!prepared.has(audio)){prepared.add(audio);preparations++;}
 return true;
}
// Compatible lifecycle hook: native playback has no graph to detach.
export function disconnectClassroomAudio(){}
export function classroomAudioOutputState(){return{mode:'native-pcm',contextState:'not-created',contextsCreated:0,warmed:false,connections:0,preparations};}
