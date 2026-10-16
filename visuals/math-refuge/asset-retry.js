// Failed speculative pages cannot start another download on every rendered frame.
export class AssetRetry {
 constructor({now=()=>performance.now(),baseDelay=2000,maxDelay=30000}={}){this.now=now;this.baseDelay=baseDelay;this.maxDelay=maxDelay;this.failed=new Map();}
 blocked(key){const failure=this.failed.get(key);return failure&&this.now()<failure.until?failure.promise:null;}
 fail(key,error){const count=(this.failed.get(key)?.count||0)+1,promise=Promise.reject(error);promise.catch(()=>{});this.failed.set(key,{count,until:this.now()+Math.min(this.maxDelay,this.baseDelay*2**(count-1)),promise});}
 clear(key){if(key===undefined)this.failed.clear();else this.failed.delete(key);}
}
