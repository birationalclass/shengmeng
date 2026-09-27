// Start cheaply on every device; model names are only a ceiling, measured frames decide promotion.
export const STARTUP_GRAPHICS={quality:'balanced',resolutionScale:'75',shadowQuality:'0',cloudQuality:'low',textureFiltering:'2',waterDetail:'low',waterReflection:'simple',oceanModel:'auto',adaptiveQuality:'auto',starEffects:'off',meteorEffects:'off',rainEffects:'off'};
export class StartupQuality{
 constructor(){this.level=0;this.retryAt=0;this.warmup=750;this.resetSamples();}
 resetSamples(){this.frames=[];this.span=0;this.good=0;}
 sample(ms,now,{targetFPS=60,gpuMs=null}={}){
  if(!Number.isFinite(ms)||ms<=0||ms>500){this.resetSamples();return false;}
  if(this.warmup>0){this.warmup-=ms;return false;}
  this.frames.push(ms);this.span+=ms;if(this.span<2000)return false;
  const sorted=[...this.frames].sort((a,b)=>a-b),target=Math.min(60,Math.max(30,targetFPS)),budget=1000/target;
  const fps=1000*this.frames.length/this.span,p95=sorted[Math.ceil(sorted.length*.95)-1];
  const good=fps>=target*.94&&p95<budget*1.4&&(gpuMs==null||gpuMs<budget*.8),slow=fps<target*.8||p95>budget*2;
  this.good=good?this.good+this.span:0;this.stats={fps,p95,target};this.frames=[];this.span=0;
  if(slow&&this.level>0){this.level--;this.retryAt=now+60000;this.good=0;this.warmup=750;return true;}
  if(this.level<2&&this.good>=4000&&now>=this.retryAt){this.level++;this.good=0;this.warmup=750;return true;}
  return false;
 }
 settings(desired){
  if(this.level===2)return {...desired,adaptiveQuality:'auto',oceanModel:'auto'};
  if(this.level===1)return {...desired,...STARTUP_GRAPHICS,resolutionScale:'100',textureFiltering:'4',cloudQuality:desired.cloudQuality==='off'?'off':'low'};
  return {...desired,...STARTUP_GRAPHICS,cloudQuality:desired.cloudQuality==='off'?'off':'low'};
 }
}
