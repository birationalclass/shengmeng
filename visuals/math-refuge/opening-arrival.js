import {motionCoordinate} from './camera-motion.js';
// World-space anchors derive from the relocated entrance, not the old campus.
export function openingArrival(start,west,z,end){
 const eye=end[1],points=[start,[west-45,eye,z],[west-3,eye,z],end];
 const durations=[5.5,4,6],velocities=[[0,0,0],[18,0,0],[3,0,0],[0,0,0]];
 return {duration:15.5,points,sample(seconds){
  let i=0,t=Math.max(0,seconds);while(i<2&&t>durations[i])t-=durations[i++];
  const u=Math.min(1,t/durations[i]),endBasis=-4*u**3+7*u**4-3*u**5;
  return points[i].map((v,axis)=>motionCoordinate(v,points[i+1][axis],velocities[i][axis],0,durations[i],u)+velocities[i+1][axis]*durations[i]*endBasis);
 }};
}
