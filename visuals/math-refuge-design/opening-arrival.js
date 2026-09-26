// Distances are physical metres; velocity is continuous at both joins.
export const DOOR_SPEED=1.2,APPROACH_SPEED=6,BRAKE_SECONDS=3;
const clamp=x=>Math.max(0,Math.min(1,x));
const ease=x=>x*x*x*(10+x*(-15+6*x));
const integral=x=>2.5*x**4-3*x**5+x**6;
// Arc-length speed envelope: start braking while the campus is still distant.
// Its spatial derivative is zero at the join, so tangential acceleration also joins at zero.
export function openingArrivalProfile(farDistance,insideDistance){
 // The extra cruise term fades out offshore; it does not alter doorway speed or acceleration.
 const envelope=d=>APPROACH_SPEED+240*(d/(d+100))**2+900*(d/(d+650))**4;
 const velocity=(time,distance)=>envelope(Math.max(0,farDistance-distance))*ease(clamp(time/2));
 const knots=[{t:0,s:0,v:0}],step=1/240;let time=0,distance=0;
 while(distance<farDistance&&time<300){
  const v=velocity(time,distance),mid=velocity(time+step/2,distance+v*step/2),next=distance+mid*step;
  const dt=next>=farDistance?(farDistance-distance)/mid:step;
  time+=dt;distance=Math.min(farDistance,next);knots.push({t:time,s:distance,v:velocity(time,distance)});
 }
 const flightSeconds=time,brakeDistance=(APPROACH_SPEED+DOOR_SPEED)*BRAKE_SECONDS/2;
 const insideSeconds=2*insideDistance/DOOR_SPEED,duration=flightSeconds+BRAKE_SECONDS+insideSeconds;
 return {brakeDistance,flightSeconds,duration,doorTime:flightSeconds+BRAKE_SECONDS,sample(time){
  if(time<flightSeconds){
   time=Math.max(0,time);let lo=0,hi=knots.length-1;
   while(hi-lo>1){const mid=(lo+hi)>>1;if(knots[mid].t<=time)lo=mid;else hi=mid;}
   const a=knots[lo],b=knots[hi],dt=b.t-a.t,u=clamp((time-a.t)/dt),u2=u*u,u3=u2*u;
   const distance=(2*u3-3*u2+1)*a.s+(u3-2*u2+u)*dt*a.v+(-2*u3+3*u2)*b.s+(u3-u2)*dt*b.v;
   const speed=((6*u2-6*u)*a.s+(-6*u2+6*u)*b.s)/dt+(3*u2-4*u+1)*a.v+(3*u2-2*u)*b.v;
   return {phase:'approach',distance,speed:Math.max(0,speed)};
  }
  if(time<flightSeconds+BRAKE_SECONDS){const t=clamp((time-flightSeconds)/BRAKE_SECONDS);
   return {phase:'brake',distance:farDistance+BRAKE_SECONDS*(APPROACH_SPEED*t+(DOOR_SPEED-APPROACH_SPEED)*integral(t)),speed:APPROACH_SPEED+(DOOR_SPEED-APPROACH_SPEED)*ease(t)};
  }
  const t=time>=duration?1:clamp((time-flightSeconds-BRAKE_SECONDS)/insideSeconds);
  return {phase:t===1?'complete':'enter',distance:farDistance+brakeDistance+DOOR_SPEED*insideSeconds*(t-integral(t)),speed:Math.max(0,DOOR_SPEED*(1-ease(t)))};
 }};
}

// Last three control points share the final straight axis: zero end curvature.
export function createOpeningRoute(T,start,end){
 const c1=start.clone().lerp(end,.48),c2=start.clone().lerp(end,.80);
 const points=[start.clone(),c1,c2,end.clone().add(new T.Vector3(-65,0,0)),end.clone().add(new T.Vector3(-28,0,0)),end.clone()];
 class ArrivalCurve extends T.Curve{getPoint(t,out=new T.Vector3()){
  out.set(0,0,0);const u=1-t,w=[u**5,5*u**4*t,10*u**3*t*t,10*u*u*t**3,5*u*t**4,t**5];
  for(let i=0;i<6;i++)out.addScaledVector(points[i],w[i]);return out;
 }}
 const route=new ArrivalCurve();route.arcLengthDivisions=4096;route.updateArcLengths();return route;
}
