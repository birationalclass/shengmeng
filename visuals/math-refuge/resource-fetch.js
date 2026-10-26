import {coursePackResponse,promoteCoursePack} from './course-pack-cache.js?v=course-packs-20261026';
import {courseResourceFetch} from './course-resource-cache.js?v=course-packs-20261026';
import {packedAssetResponse} from './board-asset-store.js?v=course-packs-20261026';
// A stalled header or body must release its request slot. No response cloning.
export function createResourceFetch(fetcher,{idleTimeout=15000,totalTimeout=0,api=globalThis,concurrency=6,backgroundLimit=2}={}){
 if(fetcher.resourceBounded)return fetcher;
 const run=async(input,options={},release=()=>{})=>{
  const controller=new AbortController(),parent=options.signal||input?.signal;
  let idle,total,reader,streamController,finished=false,rejectAbort;
  const aborted=new Promise((_,reject)=>rejectAbort=reject);aborted.catch(()=>{});
  const cleanup=()=>{api.clearTimeout(idle);api.clearTimeout(total);parent?.removeEventListener('abort',onParent);};
  const finish=()=>{if(finished)return;finished=true;cleanup();release();};
  const abort=reason=>{if(finished)return;finish();rejectAbort(reason);controller.abort(reason);reader?.cancel(reason).catch(()=>{});try{streamController?.error(reason);}catch{}};
  const onParent=()=>abort(parent.reason||new DOMException('请求已取消','AbortError'));
  const timeout=()=>abort(new DOMException('资源下载停滞，请重试。','TimeoutError'));
  const heartbeat=()=>{api.clearTimeout(idle);idle=api.setTimeout(timeout,options.resourceIdleTimeout??idleTimeout);};
  parent?.addEventListener('abort',onParent,{once:true});heartbeat();if(totalTimeout>0)total=api.setTimeout(timeout,totalTimeout);
  if(parent?.aborted)onParent();
  try{
   if(controller.signal.aborted)throw controller.signal.reason;
   const response=await Promise.race([fetcher(input,{...options,signal:controller.signal}),aborted]);
   if(!response.ok||!response.body){finish();return response;}
   reader=response.body.getReader();heartbeat();
   const body=new ReadableStream({start(c){streamController=c;},async pull(c){try{
    const {done,value}=await Promise.race([reader.read(),aborted]);
    if(done){finish();c.close();reader.releaseLock();return;}heartbeat();c.enqueue(value);
   }catch(error){finish();try{c.error(error);}catch{}}},cancel(reason){finish();controller.abort(reason);return reader.cancel(reason);}}, {highWaterMark:0});
   const result=new Response(body,{status:response.status,statusText:response.statusText,headers:response.headers});
   Object.defineProperties(result,{url:{value:response.url},redirected:{value:response.redirected},type:{value:response.type}});return result;
  }catch(error){finish();if(error.name==='TypeError')throw new Error('资源下载失败，请检查连接后重试。',{cause:error});throw error;}
 };
 const queue=[];let active=0,background=0;
 const pump=()=>{while(active<concurrency){const index=queue.findIndex(job=>!job.low||background<backgroundLimit);if(index<0)return;const job=queue.splice(index,1)[0];job.parent?.removeEventListener('abort',job.cancel);active++;if(job.low)background++;
   void run(job.input,job.options,()=>{active--;if(job.low)background--;queueMicrotask(pump);}).then(job.resolve,job.reject);
 }};
 const bounded=(input,options={})=>new Promise((resolve,reject)=>{const parent=options.signal||input?.signal;if(parent?.aborted){reject(parent.reason||new DOMException('请求已取消','AbortError'));return;}
  const job={input,options,resolve,reject,parent,low:options.priority==='low'};job.cancel=()=>{const i=queue.indexOf(job);if(i>=0){queue.splice(i,1);parent?.removeEventListener('abort',job.cancel);reject(parent.reason||new DOMException('请求已取消','AbortError'));}};
  parent?.addEventListener('abort',job.cancel,{once:true});queue.push(job);queue.sort((a,b)=>Number(a.low)-Number(b.low));pump();
 });
 bounded.promote=input=>{const target=String(input);let changed=false;for(const job of queue)if(String(job.input)===target){job.low=false;job.options={...job.options,priority:'high'};changed=true;}if(changed){queue.sort((a,b)=>Number(a.low)-Number(b.low));pump();}return fetcher.promote?.(input)||changed;};
 bounded.resourceBounded=true;return bounded;
}
const wrappers=new WeakMap();
export function resourceFetch(input,options){if(options?.signal?.aborted)return Promise.reject(options.signal.reason||new DOMException('请求已取消','AbortError'));const packed=packedAssetResponse(input?.url||input);if(packed)return Promise.resolve(packed);const fetcher=globalThis.fetch;let bounded=wrappers.get(fetcher);if(!bounded){bounded=createResourceFetch(fetcher);wrappers.set(fetcher,bounded);}const fromPack=coursePackResponse(input,options,bounded);return fromPack||courseResourceFetch(input,options,bounded);}
resourceFetch.promote=input=>{const fetcher=globalThis.fetch;const outer=wrappers.get(fetcher)?.promote?.(input)||false,inner=fetcher.promote?.(input)||false;return promoteCoursePack(input,wrappers.get(fetcher)||fetcher)||outer||inner;};
