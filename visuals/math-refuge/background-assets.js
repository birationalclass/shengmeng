// Download retries never occupy a worker or stop unrelated course assets.
export function createBackgroundAssets({load,concurrency=2,retryDelay=2000,maxDelay=30000,api=globalThis,now=()=>Date.now()}={}){
 let epoch=0,timer=null,running=null,phase='idle',freshSinceRetry=0;const jobs=new Map(),controllers=new Set();
 const clearTimer=()=>{if(timer!==null)api.clearTimeout(timer);timer=null;};
 const view=()=>{const all=[...jobs.values()],failed=all.filter(j=>j.status==='failed');return{phase,completed:all.filter(j=>j.status==='done').length,total:all.length,active:all.filter(j=>j.status==='loading').length,retrying:failed.length,errors:failed.slice(0,5).map(j=>j.error),nextRetryMs:failed.length?Math.max(0,Math.min(...failed.map(j=>j.retryAt))-now()):0};};
 function add(src,kind='asset',hint=0){if(!jobs.has(src))jobs.set(src,{src,kind,hint,status:'queued',attempts:0});}
 function schedule(){clearTimer();const failed=[...jobs.values()].filter(j=>j.status==='failed');if(!failed.length)return;const mine=epoch;timer=api.setTimeout(()=>{timer=null;if(mine===epoch)void run();},Math.max(0,Math.min(...failed.map(j=>j.retryAt))-now()));timer?.unref?.();}
 function run(){
  if(running)return running;clearTimer();const mine=epoch;phase='loading';
  const take=()=>{const all=[...jobs.values()],fresh=all.find(j=>j.status==='queued'),retry=all.find(j=>j.status==='failed'&&j.retryAt<=now());if(retry&&(!fresh||freshSinceRetry>=4)){freshSinceRetry=0;return retry;}if(fresh)freshSinceRetry++;return fresh;};
  const work=async()=>{for(;;){if(mine!==epoch)return;const job=take();if(!job)return;job.status='loading';job.attempts++;const controller=new AbortController();controllers.add(controller);
   try{await load(job,controller.signal,(...args)=>{if(mine===epoch)add(...args);});if(mine===epoch){job.status='done';job.error='';}}
   catch(error){if(mine===epoch){job.status='failed';job.error=String(error.message||error);job.retryAt=now()+Math.min(maxDelay,retryDelay*2**Math.min(12,job.attempts-1));}}
   finally{controllers.delete(controller);}
  }};
  const promise=Promise.all(Array.from({length:concurrency},work)).then(()=>{if(mine!==epoch)return null;phase=[...jobs.values()].some(j=>j.status==='failed')?'partial':'ready';schedule();return view();}).finally(()=>{if(running===promise)running=null;});running=promise;return promise;
 }
 function cancel(){epoch++;clearTimer();controllers.forEach(c=>c.abort());controllers.clear();jobs.clear();running=null;phase='idle';freshSinceRetry=0;}
 function retry(){for(const j of jobs.values())if(j.status==='failed')j.retryAt=0;return run();}
 return{add,run,retry,cancel,get state(){return view();}};
}
