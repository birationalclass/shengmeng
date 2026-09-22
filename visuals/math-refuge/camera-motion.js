// Quintic boundary-value trajectory: preserve incoming velocity/acceleration,
// arrive at rest. This avoids a speed discontinuity when a move is retargeted.
export function motionCoordinate(start,end,velocity,acceleration,duration,t){
  t=Math.max(0,Math.min(1,t));
  const t2=t*t,t3=t2*t,t4=t3*t,t5=t4*t;
  return start+(end-start)*(10*t3-15*t4+6*t5)
    +velocity*duration*(t-6*t3+8*t4-3*t5)
    +acceleration*duration*duration*.5*(t2-3*t3+3*t4-t5);
}
