// NASA reference periods; visual time is deliberately compressed, not a gravity simulation.
// https://science.nasa.gov/earth/facts/
// https://science.nasa.gov/jupiter/jupiter-facts/
// https://science.nasa.gov/neptune/neptune-facts/
// Saturn reference: https://science.nasa.gov/saturn/facts/
export const PLANET_PERIODS={
 'ring-planet':{reference:'Saturn',rotationHours:10.7,orbitDays:10756},
 'ocean-planet':{reference:'Earth',rotationHours:23.9,orbitDays:365.25},
 'gas-planet':{reference:'Jupiter',rotationHours:9.9,orbitDays:4333},
 'ice-planet':{reference:'Neptune',rotationHours:16,orbitDays:60190}
};
export function stableRandom(seed){let x=((seed+1)*9301+49297)%233280;return x/233280;}
export function planetMotion(type,seed,slot=0,hostSeed=seed){
 const p=PLANET_PERIODS[type],variation=.86+stableRandom(seed*17+13)*.28;
 const spinSeconds=(6+Math.log(p.rotationHours/9.9)*4)*variation;
 const orbitSeconds=(9+Math.log1p(p.orbitDays/365.25)*2.8)*variation*(1+slot*.1);
 return {spinSeconds,orbitSeconds,spin:4*Math.PI/spinSeconds,orbit:2*Math.PI/orbitSeconds,inclination:(stableRandom(hostSeed*43+7)-.5)*Math.PI/6,node:stableRandom(hostSeed*61+3)*Math.PI*2};
}
export function starMotion(seed){const radius=5+stableRandom(seed*11+9)*3;return {spinTilt:stableRandom(seed*29+5)*Math.PI/3,spinNode:stableRandom(seed*37+11)*Math.PI*2,spinPhase:stableRandom(seed*23+17)*Math.PI*2,radius,phase:stableRandom(seed*7+41)*Math.PI*2,orbit:2*Math.PI/(19+radius*3),inclination:0};}

export function orbitalOffset(motion,angle,radius){
 const x=Math.cos(angle)*radius,z=Math.sin(angle)*radius,c=Math.cos(motion.node),s=Math.sin(motion.node),projected=z*Math.cos(motion.inclination);
 return {x:c*x+s*projected,y:z*Math.sin(motion.inclination),z:-s*x+c*projected};
}
export function spreadStarOrbits(count,seed=0,minRadius=3.8){
 return Array.from({length:count},(_,i)=>{
  const m=starMotion(seed+i*137),fraction=(i+.15+.7*stableRandom(seed+i*53))/Math.max(1,count);
  m.radius=minRadius+7.4*fraction;m.phase=i*2.3999632297+stableRandom(seed+i*97)*.55;
  m.orbit=2*Math.PI/(19+m.radius*3);m.inclination=0;
  return m;
 });
}
