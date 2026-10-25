import {motionCoordinate} from './camera-motion.js';
const pack=pose=>{const d=pose.target.map((x,i)=>x-pose.position[i]);return [...pose.position,Math.atan2(d[2],d[0]),Math.atan2(d[1],Math.hypot(d[0],d[2])),Math.hypot(...d),pose.fov];};
const unpack=v=>{const length=Math.max(.01,v[5]),horizontal=length*Math.cos(v[4]);return {position:v.slice(0,3),target:[v[0]+horizontal*Math.cos(v[3]),v[1]+length*Math.sin(v[4]),v[2]+horizontal*Math.sin(v[3])],fov:v[6]};};
const unwrap=(angle,near)=>near+Math.atan2(Math.sin(angle-near),Math.cos(angle-near));
const matches=(a,b)=>a&&b&&a.every((value,i)=>Math.abs(value-b[i])<1e-6);
function rates(start,end,velocity,acceleration,duration,t){
 const t2=t*t,t3=t2*t,t4=t3*t,delta=end-start;
 return [delta/duration*(30*t2-60*t3+30*t4)+velocity*(1-18*t2+32*t3-15*t4)+acceleration*duration*.5*(2*t-9*t2+12*t3-5*t4),delta/(duration*duration)*(60*t-180*t2+120*t3)+velocity/duration*(-36*t+96*t2-60*t3)+acceleration*.5*(2-18*t+36*t2-20*t3)];
}
// One trajectory owns position, look target and FOV, including interrupted moves.
export class BoardCameraMotion{
 constructor(){this.reset();}
 reset(){this.segment=null;this.pose=null;this.velocity=Array(7).fill(0);this.acceleration=Array(7).fill(0);}
 sample(current,desired,dt,{immediate=false}={}){
  const start=pack(current),end=pack(desired);
  if(this.pose)start[3]=unwrap(start[3],this.pose[3]);
  end[3]=unwrap(end[3],this.segment?.end[3]??start[3]);
  if(immediate){this.reset();this.pose=end;return unpack(end);}
  if(this.pose&&!matches(start,this.pose))this.reset();
  if(!this.segment||!matches(end,this.segment.end)){
   const distance=Math.max(Math.hypot(...start.slice(0,3).map((x,i)=>x-end[i])),Math.abs(start[5]-end[5]),Math.hypot(start[3]-end[3],start[4]-end[4])*3.5,Math.abs(start[6]-end[6])/25);
   this.segment={start,end,velocity:[...this.velocity],acceleration:[...this.acceleration],duration:Math.max(.75,Math.min(5,.6+distance*.3)),elapsed:0};
  }
  const s=this.segment;s.elapsed=Math.min(s.duration,s.elapsed+Math.max(0,Math.min(.05,dt)));const t=s.elapsed/s.duration;
  this.pose=s.start.map((value,i)=>motionCoordinate(value,s.end[i],s.velocity[i],s.acceleration[i],s.duration,t));
  s.start.forEach((value,i)=>{[this.velocity[i],this.acceleration[i]]=rates(value,s.end[i],s.velocity[i],s.acceleration[i],s.duration,t);});
  return unpack(this.pose);
 }
}
