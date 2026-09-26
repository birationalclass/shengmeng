import {motionCoordinate} from './camera-motion.js';
// World-space anchors derive from the relocated entrance, not the old campus.
export function openingArrival(start,west,z,end,pavilion=null){
 const eye=end[1],points=pavilion?[start,[pavilion.x-6,eye,z],[pavilion.x+5,eye,z],[west-3,eye,z],end]:[start,[west-45,eye,z],[west-3,eye,z],end];
 const durations=pavilion?[5.5,1,4.5,4.5]:[5.5,4,6],velocities=pavilion?[[0,0,0],[12,0,0],[10,0,0],[3,0,0],[0,0,0]]:[[0,0,0],[18,0,0],[3,0,0],[0,0,0]];
 return {duration:15.5,points,sample(seconds){
  let i=0,t=Math.max(0,seconds);while(i<durations.length-1&&t>durations[i])t-=durations[i++];
  const u=Math.min(1,t/durations[i]),endBasis=-4*u**3+7*u**4-3*u**5;
  const position=points[i].map((v,axis)=>motionCoordinate(v,points[i+1][axis],velocities[i][axis],0,durations[i],u)+velocities[i+1][axis]*durations[i]*endBasis);
  if(pavilion){const u=(pavilion.bridgeX-position[0])/40;if(u>0&&u<1)position[2]=z-3*Math.sin(Math.PI*u)**2;}
  return position;
 }};
}
