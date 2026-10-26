// Download immutable compressed packs once, retain them on disk, and decode only
// the few packs in use. MP3 bytes and the existing PCM playback path are intact.
const CACHE_NAME='refuge-course-packs-v1';
const abortReason=signal=>signal?.reason||new DOMException('请求已取消','AbortError');
const keyOf=(value,base)=>{const u=new URL(value?.url||value,base);u.search='';u.hash='';return u.href;};
const hex=bytes=>[...new Uint8Array(bytes)].map(x=>x.toString(16).padStart(2,'0')).join('');
async function digest(bytes){return hex(await crypto.subtle.digest('SHA-256',bytes));}
async function unpack(bytes){
 const stream=new Blob([bytes]).stream().pipeThrough(new DecompressionStream('gzip'));
 return new Response(stream).json();
}
function join(job,signal){
 if(signal?.aborted)return Promise.reject(abortReason(signal));
 job.users++;
 return new Promise((resolve,reject)=>{
  let settled=false;
  const finish=(fn,value)=>{if(settled)return;settled=true;signal?.removeEventListener('abort',cancel);job.users--;fn(value);if(!job.done&&!job.users)job.controller.abort(new DOMException('无人等待此资源包','AbortError'));};
  const cancel=()=>finish(reject,abortReason(signal));signal?.addEventListener('abort',cancel,{once:true});
  job.promise.then(value=>finish(resolve,value),error=>finish(reject,error));
 });
}
export function createCoursePackStore({baseURL=new URL('.',import.meta.url).href,storage=globalThis.caches,decompress=unpack,hash=digest,memoryLimit=24*1024*1024,enabled=()=>typeof DecompressionStream==='function'&&!!globalThis.crypto?.subtle}={}){
 const assets=new Map(),indexes=new Map(),pending=new Map(),memory=new Map();let resident=0;
 const stats={networkPacks:0,networkBytes:0,diskHits:0,memoryHits:0,cacheErrors:0,corruptEntries:0,originalFallbacks:0};
 async function cache(){try{return await storage?.open(CACHE_NAME);}catch{stats.cacheErrors++;return null;}}
 async function getBytes(url,expected,fetcher,options){
  const disk=await cache();let bytes;
  try{const r=await disk?.match(url);if(r){bytes=await r.arrayBuffer();if((await hash(bytes)).startsWith(expected)){stats.diskHits++;return bytes;}stats.corruptEntries++;await disk.delete(url);}}catch{stats.cacheErrors++;}
  const r=await fetcher(url,{...options,cache:'force-cache'});if(!r.ok)throw Error('课程资源包下载失败：'+r.status);
  bytes=await r.arrayBuffer();if(!(await hash(bytes)).startsWith(expected))throw Error('课程资源包校验失败，请重试');
  if(options?.signal?.aborted)throw abortReason(options.signal);
  stats.networkPacks++;stats.networkBytes+=bytes.byteLength;
  try{await disk?.put(url,new Response(bytes,{headers:{'Content-Type':'application/octet-stream'}}));}catch{stats.cacheErrors++;}
  return bytes;
 }
 function remember(url,pack,size){memory.delete(url);memory.set(url,{pack,size});resident+=size;while(resident>memoryLimit&&memory.size>1){const [k,v]=memory.entries().next().value;memory.delete(k);resident-=v.size;}return pack;}
 function load(item,fetcher,options={}){
  if(options.signal?.aborted)return Promise.reject(abortReason(options.signal));
  const hit=memory.get(item.url);if(hit){memory.delete(item.url);memory.set(item.url,hit);stats.memoryHits++;return Promise.resolve(hit.pack);}
  let job=pending.get(item.url);
  if(job?.controller.signal.aborted){pending.delete(item.url);job=null;}
  if(job){if(options.priority!=='low')fetcher.promote?.(item.url);return join(job,options.signal);}
  job={controller:new AbortController(),users:0,done:false};
  job.promise=(async()=>{
   const bytes=await getBytes(item.url,item.sha256,fetcher,{...options,signal:job.controller.signal});const pack=await decompress(bytes);
   if(pack.version!==2||!pack.assets||Array.isArray(pack.assets))throw Error('课程资源包格式无效');
   for(const path of item.files)if(typeof pack.assets[path]?.body!=='string')throw Error('课程资源包缺少文件');
   return remember(item.url,pack,item.expandedBytes||bytes.byteLength);
  })().finally(()=>{job.done=true;if(pending.get(item.url)===job)pending.delete(item.url);});
  pending.set(item.url,job);return join(job,options.signal);
 }
 async function register(program,{fetcher=globalThis.fetch,base=baseURL}={}){
  if(!program?.resourceIndex||!enabled())return false;
  const url=new URL(program.resourceIndex,base).href;
  if(indexes.has(url))return indexes.get(url);
  const promise=(async()=>{
   const expected=url.match(/-([a-f0-9]{20})\.json$/)?.[1];if(!expected)throw Error('课程资源索引须使用内容版本');
   const data=JSON.parse(new TextDecoder().decode(await getBytes(url,expected,fetcher,{priority:'high'})));
   if(data.version!==1||!Array.isArray(data.packs))throw Error('课程资源索引无效');
   const root=new URL(data.base,url).href,items=data.packs.map(p=>({...p,url:new URL(p.url,root).href}));
   for(const item of items){if(!/^[a-f0-9]{64}$/.test(item.sha256))throw Error('课程资源包校验值无效');for(const file of item.files){const asset=keyOf(file,root);if(!asset.startsWith(root))throw Error('课程资源路径越界');assets.set(asset,{item,file});}}
   return {id:data.id,items,groups:data.groups,root,indexURL:url};
  })().catch(error=>{indexes.delete(url);throw error;});indexes.set(url,promise);return promise;
 }
 function response(input,options={},fetcher=globalThis.fetch){
  const target=assets.get(keyOf(input,baseURL));if(!target||!enabled())return null;
  return load(target.item,fetcher,options).then(pack=>{
   if(options.signal?.aborted)throw abortReason(options.signal);
   const entry=pack.assets[target.file],body=Uint8Array.from(atob(entry.body),c=>c.charCodeAt(0));
   return new Response(body,{headers:{'Content-Type':entry.type,'Content-Length':String(body.byteLength)}});
  }).catch(error=>{if(options.signal?.aborted)throw abortReason(options.signal);stats.originalFallbacks++;return fetcher(input,options);});
 }
 async function download(program,{fetcher=globalThis.fetch,onProgress=()=>{},signal}={}){
  const index=await register(program,{fetcher});if(!index)throw Error('此浏览器请使用完整离线包');
  const disk=await cache();if(!disk)throw Error('浏览器存储不可用，无法保存整课');
  // Only include shared shards reached by this course; explicit download also
  // saves all mapped shared assets so a newly exposed diagram label is ready.
  let next=0,done=0;onProgress({completed:0,total:index.items.length});
  await Promise.all(Array.from({length:2},async()=>{while(next<index.items.length){if(signal?.aborted)throw abortReason(signal);await load(index.items[next++],fetcher,{signal,priority:'low'});onProgress({completed:++done,total:index.items.length});}}));
  for(const url of [index.indexURL,...index.items.map(p=>p.url)]){const saved=await disk.match(url);if(!saved)throw Error('课程尚未完整保存，请检查浏览器存储空间');await saved.body?.cancel();}return true;
 }
 return {register,response,download,promote(input,fetcher){const item=assets.get(keyOf(input,baseURL))?.item;return item?fetcher.promote?.(item.url)||false:false;},get state(){return {...stats,residentBytes:resident,residentPacks:memory.size,pendingPacks:pending.size,mappedFiles:assets.size};}};
}
const store=createCoursePackStore();
export const configureCoursePacks=(program,options)=>store.register(program,options);
export const coursePackResponse=(input,options,fetcher)=>store.response(input,options,fetcher);
export const downloadCoursePacks=(program,options)=>store.download(program,options);
export const promoteCoursePack=(input,fetcher)=>store.promote(input,fetcher);
export const coursePackState=()=>store.state;
