// CloudBase HTTP gateway; no third-party browser SDK is needed.
export function createRecordsApi({config,t,fetchImpl=fetch}){
 return async function api(path,{method='GET',body,token,signal}={}){
  const controller=new AbortController(),abort=()=>controller.abort(signal?.reason);let timer;
  try{
   if(signal?.aborted)abort();else signal?.addEventListener('abort',abort,{once:true});
   const timeout=new Promise((_,reject)=>{
    controller.signal.addEventListener('abort',()=>reject(Object.assign(Error(t('连接超时，请点击刷新或重试。','Connection timed out. Please refresh or retry.')),{name:'AbortError'})),{once:true});
    timer=setTimeout(()=>controller.abort(),20000);
    if(controller.signal.aborted)reject(Object.assign(Error('Aborted'),{name:'AbortError'}));
   });
   const request=(async()=>{
    if(!config.url)throw Object.assign(Error(t('通关登记尚未开放：正在配置服务器。','Server setup is in progress.')),{status:503});
    const response=await fetchImpl(config.url+path,{method,headers:{...(body?{'Content-Type':'application/json'}:{}),...(token?{Authorization:'Bearer '+token}:{})},...(body?{body:JSON.stringify(body)}:{}),signal:controller.signal,cache:'no-store',credentials:'omit',referrerPolicy:'no-referrer'});
    const data=await response.json();if(!response.ok)throw Object.assign(Error(data.error),{status:response.status});return data;
   })();
   return await Promise.race([request,timeout]);
  }catch(error){
   if(error.status||error.name==='AbortError')throw error;
   throw Error(t('暂时无法连接通关服务器，请检查网络后点击刷新或重试。','Unable to reach the records server. Check your connection and retry.'));
  }finally{clearTimeout(timer);signal?.removeEventListener('abort',abort);}
 };
}
