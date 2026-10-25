import {motionCoordinate} from './camera-motion.js';
import {PHASE_SECONDS} from './lecture-state.js?v=uniform-review-20261019';
const clamp=value=>Math.max(0,Math.min(1,Number(value)||0));
function rates(start,end,v,a,d,t){const t2=t*t,t3=t2*t,t4=t3*t,delta=end-start;return[delta/d*(30*t2-60*t3+30*t4)+v*(1-18*t2+32*t3-15*t4)+a*d*.5*(2*t-9*t2+12*t3-5*t4),delta/(d*d)*(60*t-180*t2+120*t3)+v/d*(-36*t+96*t2-60*t3)+a*.5*(2-18*t+36*t2-20*t3)];}
// Each board pair starts and stops at rest instead of jumping to full lift speed.
export class BoardLiftMotion{
 constructor(value=0,duration=PHASE_SECONDS.lift){this.duration=duration;this.reset(value);}
 reset(value=0){this.value=clamp(value);this.velocity=0;this.acceleration=0;this.segment=null;this.paused=null;return this.value;}
 step(current,target,dt,{immediate=false,paused=false}={}){
  current=clamp(current);target=clamp(target);
  if(immediate)return this.reset(target);
  if(Math.abs(current-this.value)>1e-8)this.reset(current);
  if(Math.abs(current-target)<1e-12&&Math.abs(this.velocity)+Math.abs(this.acceleration)<1e-8)return this.reset(target);
  if(paused){if(!this.paused)this.paused={target:this.segment?.end??target,remaining:this.segment?Math.max(.1,this.segment.duration-this.segment.elapsed):this.duration*Math.abs(target-current)};this.segment=null;this.velocity=0;this.acceleration=0;this.value=current;return current;}
  const resume=this.paused;this.paused=null;
  if(!this.segment||this.segment.end!==target){
   const duration=resume&&resume.target===target?resume.remaining:Math.max(.4,this.duration*Math.abs(target-current));
   this.segment={start:current,end:target,velocity:this.velocity,acceleration:this.acceleration,duration,elapsed:0};
  }
  const s=this.segment;s.elapsed=Math.min(s.duration,s.elapsed+Math.max(0,Math.min(.05,dt)));
  if(s.elapsed+1e-9>=s.duration)return this.reset(target);
  const t=s.elapsed/s.duration,raw=motionCoordinate(s.start,s.end,s.velocity,s.acceleration,s.duration,t);this.value=clamp(raw);
  [this.velocity,this.acceleration]=rates(s.start,s.end,s.velocity,s.acceleration,s.duration,t);
  if(raw!==this.value){this.velocity=0;this.acceleration=0;}
  return this.value;
 }
}
