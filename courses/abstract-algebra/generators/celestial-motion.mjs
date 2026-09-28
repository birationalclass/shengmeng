// NASA reference periods; visual time is deliberately compressed, not a gravity simulation.
// https://science.nasa.gov/earth/facts/
// https://science.nasa.gov/jupiter/jupiter-facts/
// https://science.nasa.gov/neptune/neptune-facts/
export const PLANET_PERIODS={
 'ocean-planet':{reference:'Earth',rotationHours:23.9,orbitDays:365.25},
 'gas-planet':{reference:'Jupiter',rotationHours:9.9,orbitDays:4333},
 'ice-planet':{reference:'Neptune',rotationHours:16,orbitDays:60190}
};
export function stableRandom(seed){let x=((seed+1)*9301+49297)%233280;return x/233280;}
export function planetMotion(type,seed,slot=0){
 const p=PLANET_PERIODS[type],variation=.86+stableRandom(seed*17+13)*.28;
 const spinSeconds=(6+Math.log(p.rotationHours/9.9)*4)*variation;
 const orbitSeconds=(9+Math.log1p(p.orbitDays/365.25)*2.8)*variation*(1+slot*.1);
 return {spinSeconds,orbitSeconds,spin:2*Math.PI/spinSeconds,orbit:2*Math.PI/orbitSeconds};
}
export function starMotion(seed){const radius=5+stableRandom(seed*11+9)*3;return {radius,phase:stableRandom(seed*7+41)*Math.PI*2,orbit:2*Math.PI/(19+radius*3),inclination:(stableRandom(seed*19)-.5)*.15};}
