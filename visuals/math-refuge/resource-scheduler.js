// Optional work runs only between settled frames. No timeout can bypass the opening gate.
export class ResourceScheduler {
 constructor({policy=()=>({}),report=()=>{},api=globalThis}={}){this.policy=policy;this.report=report;this.api=api;this.jobs=new Map();this.queue=[];this.active=null;this.cpuMs=0;this.frameMs=0;this.renderMs=0;this.lastFrame=0;this.running=false;}
 frame(frameMs,renderMs,now=this.now()){if(frameMs>0&&frameMs<250)this.frameMs=this.frameMs?this.frameMs*.9+frameMs*.1:frameMs;this.renderMs=this.renderMs?this.renderMs*.9+renderMs*.1:renderMs;this.lastFrame=now;}
 now(){return this.api.performance?.now()??Date.now();}
 snapshot(){const p=this.policy(),target=1000/(p.targetFPS||60);return {active:Boolean(this.active),content:this.active?.label||'空闲 · 按需准备',pending:this.queue.length,cpuMs:this.active?this.cpuMs:0,frameMs:this.frameMs,renderMs:this.renderMs,frameBudget:target,protected:Boolean(p.opening),paused:Boolean(this.active&&!this.allowed(this.active)),error:this.error||''};}
 allowed(job){const p=this.policy();if(job.priority<2)return true;return Boolean(p.entered&&p.foreground!==false&&!p.opening&&!p.moving);}
 enqueue(key,label,factory,{priority=2}={}){if(this.jobs.has(key))return this.jobs.get(key);let resolve,reject;const promise=new Promise((a,b)=>{resolve=a;reject=b;});this.jobs.set(key,promise);this.queue.push({key,label,factory,priority,resolve,reject});this.queue.sort((a,b)=>a.priority-b.priority);void this.pump();return promise;}
 async turn(job){for(;;){if(!this.allowed(job)){this.report(this.snapshot());await new Promise(r=>this.api.setTimeout(r,100));continue;}
   // Required work must not wait for idle time: a busy render loop may never offer it.
   // Optional timeout only grants a tiny turn; the opening/movement gate is rechecked.
   await new Promise(r=>{if(job.priority<2)this.api.setTimeout(r,0);else if(this.api.requestIdleCallback)this.api.requestIdleCallback(r,{timeout:250});else this.api.setTimeout(r,32);});
   if(!this.allowed(job))continue;return;
  }}
 async pump(){if(this.running)return;this.running=true;
  while(this.queue.length){const job=this.active=this.queue.shift();try{
    await this.turn(job);let start=this.now(),result=job.factory();this.cpuMs=this.now()-start;
    if(result&&typeof result.next==='function'){
      for(;;){await this.turn(job);start=this.now();const step=result.next();this.cpuMs=this.now()-start;const next=await step;if(next.done)break;
        if(typeof next.value==='function'){await this.turn(job);start=this.now();const value=next.value();this.cpuMs=this.now()-start;await value;}else await next.value;
        this.report(this.snapshot());
        // A slow frame or an expensive indivisible step reduces the loading duty cycle.
        const target=1000/(this.policy().targetFPS||60);if(job.priority>=2&&(this.frameMs>target*1.2||this.cpuMs>2))await new Promise(r=>this.api.setTimeout(r,100));
      }
    }else await result;
    job.resolve();
   }catch(error){this.error=job.label+'：'+error.message;this.jobs.delete(job.key);job.reject(error);}
   this.active=null;this.report(this.snapshot());
  }this.running=false;
 }
}
