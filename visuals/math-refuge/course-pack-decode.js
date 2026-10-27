const turn=()=>globalThis.scheduler?.yield?globalThis.scheduler.yield():new Promise(resolve=>setTimeout(resolve,0));
const cancellation=signal=>signal?.reason||new DOMException('请求已取消','AbortError');
// Audio entries are several MiB. Uint8Array.from(binary, callback) allocated
// per-character intermediates and stalled the entry camera for ~0.5 seconds.
export async function decodeCourseBase64(text,{signal,native=typeof Uint8Array.fromBase64==='function'?value=>Uint8Array.fromBase64(value):null,yieldTask=turn,chunkBytes=256*1024}={}){
 if(signal?.aborted)throw cancellation(signal);
 if(native)return native(text);
 const binary=atob(text),bytes=new Uint8Array(binary.length);
 for(let start=0;start<binary.length;start+=chunkBytes){
  const end=Math.min(binary.length,start+chunkBytes);
  for(let i=start;i<end;i++)bytes[i]=binary.charCodeAt(i);
  if(end<binary.length){await yieldTask();if(signal?.aborted)throw cancellation(signal);}
 }
 return bytes;
}
