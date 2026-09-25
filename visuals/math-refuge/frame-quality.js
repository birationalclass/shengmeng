// Whole-scene fallback driven by presented frame cadence, not GPU extensions.
// Keep sampling while the monitor is closed, but discard background-tab pauses.
export class FrameQuality{
 constructor(){this.reset();}
 reset(){this.level=0;this.refresh=60;this.changedAt=0;this.retryAt=0;this.recovering=false;this.resetSamples();}
 resetSamples(){this.frames=[];this.span=0;this.good=0;this.bad=0;this.stats=null;}
 sample(ms,now,{active=true,enabled=true,targetFPS=60}={}){
  if(!enabled){if(this.level||this.stats)this.reset();return;}
  if(!active||!Number.isFinite(ms)||ms<=0||ms>2000){this.resetSamples();return;}
  if(targetFPS!==this.targetFPS){this.targetFPS=targetFPS;this.resetSamples();}
  this.frames.push(ms);this.span+=ms;if(this.span<2000)return;
  const sorted=[...this.frames].sort((a,b)=>a-b),fast=sorted[Math.floor(sorted.length*.2)];
  if(fast<11)this.refresh=120;
  const target=Math.min(Math.max(30,targetFPS),this.refresh),budget=1000/target;
  const fps=1000*this.frames.length/this.span,p95=sorted[Math.ceil(sorted.length*.95)-1],span=this.span;
  this.frames=[];this.span=0;this.stats={fps,p95,target};
  const slow=fps<target*.88||p95>budget*1.8;
  this.bad=slow?this.bad+span:0;
  this.good=!slow&&fps>=target*.96&&p95<budget*1.3?this.good+span:0;
  if(this.level<5&&(this.bad>=4000||slow&&this.recovering||fps<target*.55)){
   this.level++;this.changedAt=now;this.good=this.bad=0;
   if(this.recovering)this.retryAt=now+60000;
   this.recovering=false;
  }else if(this.level>0&&this.good>=20000&&now>=this.retryAt&&now-this.changedAt>=20000){
   this.level--;this.changedAt=now;this.good=this.bad=0;this.recovering=true;
  }
 }
 settings({reading=false,cloud='medium',shadow=2048}={}){
  return {
   scale:Math.max(reading?.75:.7,[1,1,1,.9,.8,.7][this.level]),
   cloud:this.level>=2?'off':this.level>=1&&cloud!=='off'?'low':cloud,
   shadow:this.level>=2?0:this.level>=1?Math.min(shadow,1024):shadow,
   simpleWater:this.level>=1,particles:this.level<2,
  };
 }
}
