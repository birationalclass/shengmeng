// A durable, per-account outbox. A retry always keeps its original submission ID.
export function shouldSubmitAttempt(attempt,journey){
 return (journey[attempt.key]?.passed||0)<=attempt.stage;
}
export function createGeneratorSync({api,read,write,getAccount,getJourney=()=>({}),onProgress,onStatus=()=>{}}){
 let session=null,busy=false,timer;
 const key=id=>'generators-outbox-v1:'+id;
 async function flush(){
  if(busy||!session||session.account.id!==getAccount().id)return;
  busy=true;const own=session;clearTimeout(timer);
  try{
   let queue=read(key(own.account.id))||[];
   while(queue.length){
    if(session!==own||getAccount().id!==own.account.id)return;
    const result=await api('/api/generators/attempts',{method:'POST',token:own.sessionToken,body:queue[0]});
    const latest=read(key(own.account.id))||[];write(key(own.account.id),latest.filter(x=>x.submissionId!==queue[0].submissionId));
    if(session===own&&getAccount().id===own.account.id)onProgress(result);
    queue=read(key(own.account.id))||[];
   }
   const result=await api('/api/generators/progress',{token:own.sessionToken});
   if(session===own&&getAccount().id===own.account.id){onProgress(result);onStatus('synced');}
  }catch(error){onStatus('pending',error.message);if(!error.status||error.status>=500||error.status===429)timer=setTimeout(flush,30000);}
  finally{busy=false;if(session!==own)void flush();}
 }
 return {flush,setSession(value){session=value;void flush();},enqueue(attempt){if(!shouldSubmitAttempt(attempt,getJourney()))return false;const id=getAccount().id;write(key(id),[...(read(key(id))||[]),{...attempt,submissionId:crypto.randomUUID()}]);onStatus('pending');void flush();return true;}};
}
