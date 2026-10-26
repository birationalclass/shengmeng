// Keep encoded resources for the selected course; decoded canvases stay windowed.
let course=null,resources=null,retainedBytes=0;const pending=new Map();
export function retainCourseResources(id){if(course!==id){course=id;resources=new Map();retainedBytes=0;pending.clear();}}
export function courseResourceState(){return{course,files:resources?.size||0,bytes:retainedBytes};}
export async function courseResourceFetch(input,options,fetcher){
 if(!resources)return fetcher(input,options);
 const url=new URL(String(input?.url||input),globalThis.document?.baseURI||globalThis.location?.href||'https://refuge.local/');url.hash='';
 const key=url.href,store=resources;
 if(store.has(key)){const r=store.get(key);return new Response(r.body,{status:r.status,headers:r.headers});}
 // Concurrent readers share bytes but each receives its own Response.
 if(!pending.has(key)){
  const job=(async()=>{const response=await fetcher(input,options);if(!response.ok)return response;const record={body:await response.arrayBuffer(),status:response.status,headers:[...response.headers]};store.set(key,record);if(store===resources)retainedBytes+=record.body.byteLength;return record;})();
  pending.set(key,job);job.finally(()=>{if(pending.get(key)===job)pending.delete(key);}).catch(()=>{});
 }
 const result=await pending.get(key);if(result instanceof Response)return result;
 return new Response(result.body,{status:result.status,headers:result.headers});
}
