// Foreground frame cadence works even where Safari exposes no GPU timer.
// Test progressively, back off quickly, and never retry a failed tier every few seconds.
export class OceanBudget{
 constructor(){this.level=0;this.refresh=60;this.retryAfter=0;this.failures=0;this.resetSamples();}
 resetSamples(){this.frames=[];this.span=0;this.good=0;this.bad=0;this.stats=null;}
 configure(mode='auto',target=60){
  if(this.mode===mode&&this.target===target)return;
  this.mode=mode;this.target=target;this.level=mode==='study'?2:mode==='classic'?1:0;
  this.retryAfter=0;this.failures=0;this.resetSamples();
 }
 sample(ms,now,{active=true,eligible=true,gpuMs=null}={}){
  if(!active||!Number.isFinite(ms)||ms<=0||ms>2000){this.resetSamples();return this.level;}
  if(this.mode!=='auto')return this.level;
  this.frames.push(ms);this.span+=ms;
  if(this.span<2000)return this.level;
  const sorted=[...this.frames].sort((a,b)=>a-b),fast=sorted[Math.floor(sorted.length*.2)];
  // A 60 Hz browser cannot satisfy a 120 FPS target; never penalize it for that.
  if(fast<11)this.refresh=120;
  const target=Math.min(this.target||60,this.refresh),budget=1000/target;
  const fps=this.frames.length*1000/this.span,p95=sorted[Math.ceil(sorted.length*.95)-1],elapsed=this.span;
  this.frames=[];this.span=0;this.stats={fps,p95,target};
  const slow=fps<target*.85||p95>budget*1.8;
  this.bad=slow?this.bad+elapsed:0;
  this.good=!slow&&eligible&&fps>=target*.94&&p95<budget*1.3&&(gpuMs==null||gpuMs<budget*.75)?this.good+elapsed:0;
  if(this.level>0&&(this.bad>=4000||fps<target*.55)){
   this.level=fps<target*.55?0:this.level-1;
   this.failures++;this.retryAfter=now+Math.min(300000,60000*this.failures);
   this.bad=this.good=0;
  }else if(this.level<2&&this.good>=16000&&now>=this.retryAfter){
   this.level++;this.good=this.bad=0;
  }
  return this.level;
 }
}
