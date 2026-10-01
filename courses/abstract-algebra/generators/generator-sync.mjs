// A durable, per-account outbox. A retry always keeps its original submission ID.
export function shouldSubmitAttempt(attempt,journey){
 return (journey[attempt.key]?.passed||0)<=attempt.stage;
}
export function createGeneratorSync({api,read,write,getAccount,getJourney=()=>({}),onProgress,onStatus=()=>{}}){
 let session=null,busy=false,timer,inFlight=null,failed=false,resetting=false;
 const key=id=>'generators-outbox-v1:'+id;
 function flush(){
  if(resetting)return Promise.resolve();if(inFlight)return inFlight;
  let initial;failed=false;
  inFlight=Promise.resolve().then(()=>{initial=session;return runFlush();}).finally(()=>{inFlight=null;if(session!==initial||(!failed&&session&&session.account.id===getAccount().id&&(read(key(session.account.id))||[]).length))void flush();});
  return inFlight;
 }
 async function runFlush(){
  if(busy||!session||session.account.id!==getAccount().id)return;
  busy=true;const own=session;clearTimeout(timer);timer=null;
  try{
   const epochKey='generators-epoch-v1:'+own.account.id;
   const remote=await api('/api/generators/progress',{token:own.sessionToken});
   if(session!==own||getAccount().id!==own.account.id)return;
   if((remote.epoch||0)!==(read(epochKey)||0)){write(key(own.account.id),[]);write(epochKey,remote.epoch||0);onProgress({...remote,reset:true});}
   let queue=read(key(own.account.id))||[];
   while(queue.length){
    if(session!==own||getAccount().id!==own.account.id)return;
    const result=await api('/api/generators/attempts',{method:'POST',token:own.sessionToken,body:{...queue[0],epoch:read(epochKey)||0}});
    const latest=read(key(own.account.id))||[];write(key(own.account.id),latest.filter(x=>x.submissionId!==queue[0].submissionId));
    if(session===own&&getAccount().id===own.account.id)onProgress(result);
    queue=read(key(own.account.id))||[];
   }
   const latest=await api('/api/generators/progress',{token:own.sessionToken});
   if(session!==own||getAccount().id!==own.account.id)return;
   const snapshot=JSON.parse(JSON.stringify(getJourney())),better=Object.entries(snapshot).some(([k,v])=>(v.passed||0)>(latest.journey?.[k]?.passed||0));
   const result=better?await api('/api/generators/sync',{method:'POST',token:own.sessionToken,body:{journey:snapshot,consumedLives:read('generators-consumed-v1:'+own.account.id)||0,epoch:read(epochKey)||0}}):latest;
   if((result.epoch||0)!==(read(epochKey)||0)){result.reset=true;write(key(own.account.id),[]);}
   if(!result.reset)for(const [k,v] of Object.entries(getJourney()))if((v.passed||0)>(snapshot[k]?.passed||0))result.journey[k]=v;
   if(session===own&&getAccount().id===own.account.id){write(epochKey,result.epoch||0);onProgress({...result,authoritative:true});onStatus('synced');}
  }catch(error){onStatus('pending',error.message);failed=true;if(!error.status||error.status>=500||error.status===429)timer=setTimeout(flush,30000);}
  finally{busy=false;}
 }
 async function reset(){
  if(!session||session.account.id!==getAccount().id)throw Error('请先连接服务器后再清除记录。');
  const own=session;resetting=true;clearTimeout(timer);
  try{await inFlight;if(session!==own||getAccount().id!==own.account.id)throw Error('账号已切换，请重试。');
   const current=await api('/api/generators/progress',{token:own.sessionToken});
   const result=await api('/api/generators/reset',{method:'POST',token:own.sessionToken,body:{confirm:true,epoch:current.epoch||0}});
   write(key(own.account.id),[]);write('generators-consumed-v1:'+own.account.id,0);
   if(session===own&&getAccount().id===own.account.id){write('generators-epoch-v1:'+own.account.id,result.epoch);onProgress({...result,reset:true});}
  }finally{resetting=false;}
 }
 return {flush,reset,setSession(value){session=value;void flush();},enqueue(attempt){if(resetting||!shouldSubmitAttempt(attempt,getJourney()))return false;const id=getAccount().id;if(attempt.won===false)write('generators-consumed-v1:'+id,(read('generators-consumed-v1:'+id)||0)+1);write(key(id),[...(read(key(id))||[]),{...attempt,submissionId:crypto.randomUUID()}]);onStatus('pending');void flush();return true;}};
}
