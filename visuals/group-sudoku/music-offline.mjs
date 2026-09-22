import {CHUNK_SIZE,TRACK_URL,readMeta,saveChunk,clearTrack} from './music-cache.mjs';

export async function downloadTrack({signal,onProgress,fetcher=fetch,store={readMeta,saveChunk,clearTrack}}){
 let meta=await store.readMeta();
 if(meta?.complete){onProgress(meta);return;}
 let offset=meta?.bytes||0;
 while(!meta?.complete){
  signal.throwIfAborted();
  const headers={Range:`bytes=${offset}-${offset+CHUNK_SIZE-1}`};
  if(meta?.validator)headers['If-Range']=meta.validator;
  const response=await fetcher(TRACK_URL+'?offline-download=1',{headers,signal,cache:'no-store'});
  const range=/^bytes (\d+)-(\d+)\/(\d+)$/.exec(response.headers.get('Content-Range')||'');
  const etag=response.headers.get('ETag'),validator=etag&&!etag.startsWith('W/')?etag:response.headers.get('Last-Modified');
  // Never read a 200 full-track response into memory, even if a server ignores Range.
  if(response.status!==206||!range){await response.body?.cancel();if(meta)await store.clearTrack();throw new Error('range');}
  const [from,to,total]=range.slice(1).map(Number);
  if(from!==offset||to!==Math.min(offset+CHUNK_SIZE,total)-1||!Number.isSafeInteger(total)||total<=0||total>256*1024*1024||meta&&(meta.total!==total||meta.validator!==validator)){
   await response.body?.cancel();await store.clearTrack();throw new Error('changed');
  }
  // Bound even a malformed response body to one chunk.
  const reader=response.body.getReader(),parts=[];let size=0;
  try{while(true){signal.throwIfAborted();const {done,value}=await reader.read();if(done)break;size+=value.byteLength;if(size>CHUNK_SIZE)throw new Error('range');parts.push(value);}}
  finally{await reader.cancel().catch(()=>{});reader.releaseLock();}
  if(size!==to-from+1)throw new Error('truncated');signal.throwIfAborted();
  const blob=new Blob(parts,{type:'audio/mpeg'});
  meta={total,bytes:to+1,validator,complete:to+1===total};
  await store.saveChunk(Math.floor(offset/CHUNK_SIZE),blob,meta);offset=meta.bytes;onProgress(meta);
 }
}

export function createOfflineMusic({t}){
 const button=document.getElementById('musicDownload');if(!button)return;
 const remove=document.getElementById('musicCacheClear'),progress=document.getElementById('musicDownloadProgress'),note=document.getElementById('musicOfflineStatus');
 let meta=null,controller=null,ready=false,error='',persistent=false;
 const supported=isSecureContext&&'serviceWorker'in navigator&&'indexedDB'in globalThis&&'ReadableStream'in globalThis;
 function sync(){
  const active=!!controller,percent=meta?.total?Math.floor(meta.bytes/meta.total*100):0;
  button.textContent=active?t('暂停下载','Pause download'):meta?.complete?t('离线音乐已就绪','Offline music ready'):meta?.bytes?t('继续下载 · '+percent+'%','Resume download · '+percent+'%'):t('下载离线音乐 · 41 MB','Download offline music · 41 MB');
  button.disabled=!ready||!!meta?.complete;remove.disabled=!ready||active||!meta?.bytes;
  remove.textContent=t('清除音乐缓存','Clear music cache');
  progress.hidden=!meta?.bytes||meta.complete;progress.value=percent;progress.setAttribute('aria-label',t('离线音乐下载进度','Offline music download progress'));
  note.textContent=!supported?t('此浏览器暂不支持离线音乐，仍可在线播放。','Offline music is unavailable in this browser; streaming still works.'):error||(!ready?t('正在准备离线功能…','Preparing offline support…'):meta?.complete?t('已保存到本机，播放优先使用离线音乐。','Saved on this device; playback now prefers offline music.')+(persistent?'':t(' 浏览器可能清理缓存。',' The browser may evict this cache.')):active?t('下载中，可随时暂停；已下载部分会保留。','Downloading. Pause anytime; completed chunks are kept.'):meta?.bytes?t('已暂停，可继续下载。完整下载后可离线听。','Paused. Resume to make the full recording available offline.'):t('只下载音乐，不包含离线登录和游戏资源。','Music only; offline login and game assets are not included.'));
 }
 async function exclusive(task){
  if(navigator.locks)return navigator.locks.request('group-sudoku-music-download',{ifAvailable:true},lock=>{if(!lock)throw new Error('busy');return task();});
  // Older browsers without Web Locks: writes are atomic and identical chunks use identical keys.
  return task();
 }
 function message(e){return e.name==='QuotaExceededError'?t('本机空间不足，请清理空间后重试。','Device storage is full. Free some space and retry.'):e.message==='busy'?t('另一个标签页正在处理音乐，请稍后重试。','Another tab is managing music. Please retry later.'):['range','changed'].includes(e.message)?t('下载源发生变化或不支持分段读取，请重试。','The source changed or does not support byte ranges. Retry download.'):t('下载中断，已保存的部分可继续下载。','Download interrupted. Saved chunks can be resumed.');}
 button.addEventListener('click',async()=>{
  if(controller){controller.abort();return;}
  controller=new AbortController();error='';sync();
  try{
   // Ask for persistence only in response to the explicit offline-download gesture.
   const persistence=navigator.storage?.persist?.().catch(()=>false);
   await exclusive(async()=>{
    meta=await readMeta();const estimate=await navigator.storage?.estimate?.();
    if(estimate?.quota&&estimate.quota-estimate.usage<(meta?.total||41043789)-(meta?.bytes||0)+CHUNK_SIZE)throw new DOMException('No space','QuotaExceededError');
    await downloadTrack({signal:controller.signal,onProgress:value=>{meta=value;sync();}});
   });
   persistent=!!await persistence;if(meta?.complete)window.dispatchEvent(new Event('music-cache-change'));
  }catch(e){if(e.name!=='AbortError')error=message(e);}
  finally{controller=null;try{meta=await readMeta();}catch{}sync();}
 });
 remove.addEventListener('click',async()=>{remove.disabled=true;try{await exclusive(clearTrack);meta=null;error='';window.dispatchEvent(new Event('music-cache-change'));}catch(e){error=message(e);}sync();});
 window.addEventListener('course-language',sync);
 window.addEventListener('pagehide',()=>controller?.abort());
 window.addEventListener('focus',()=>{if(ready&&!controller)readMeta().then(value=>{meta=value;sync();}).catch(()=>{});});
 sync();
 if(supported)(async()=>{
  try{
   await navigator.serviceWorker.register(new URL('./music-worker.mjs',import.meta.url),{type:'module',scope:'./',updateViaCache:'none'});
   await new Promise((resolve,reject)=>{
    const done=()=>{if(navigator.serviceWorker.controller?.scriptURL===new URL('./music-worker.mjs',import.meta.url).href){clearTimeout(timer);navigator.serviceWorker.removeEventListener('controllerchange',done);resolve();}};
    const timer=setTimeout(()=>{navigator.serviceWorker.removeEventListener('controllerchange',done);reject(new Error('worker'));},15000);
    navigator.serviceWorker.addEventListener('controllerchange',done);done();
   });
   meta=await readMeta();persistent=!!await navigator.storage?.persisted?.();ready=true;
  }catch{error=t('离线功能暂不可用，在线播放不受影响；刷新可重试。','Offline support is unavailable. Streaming still works; reload to retry.');}
  sync();
 })();
}
