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
export function spreadStarOrbits(count,seed=0,minRadius=3.8,asymmetric=false){
 const placed=[];return Array.from({length:count},(_,i)=>{
  const m=starMotion(seed+i*137),fraction=(i+.15+.7*stableRandom(seed+i*53))/Math.max(1,count);
  m.radius=minRadius+Math.max(12,minRadius*1.2,count*.65)*fraction;m.phase=i*2.3999632297+stableRandom(seed)*Math.PI*2;
  if(asymmetric){
   const arm=i%3,u=Math.floor(i/3)/Math.max(1,Math.ceil(count/3)-1);
   m.radius=minRadius+(arm===0?2:arm===1?6:10)+u*(arm===0?21:arm===1?14:12);
   m.phase=[.15,2.35,4.6][arm]+u*[1.7,.95,.65][arm]+(stableRandom(seed+i*79)-.5)*.18;
   for(let attempt=0;attempt<30;attempt++){const x=Math.cos(m.phase)*m.radius,z=Math.sin(m.phase)*m.radius;if(placed.every(p=>Math.hypot(x-p.x,z-p.z)>3.3)){placed.push({x,z});break;}m.phase+=.12;}
  }
  m.orbit=2*Math.PI/(22+minRadius*2);m.inclination=0;
  return m;
 });
}

// Shared world-space geometry: all galaxy sizes use the same clearance and packing rules.
export function planetOrbitRadius(hostRadius,planetRadius,element,galaxy,slot){
 return (hostRadius+planetRadius)*(1.75+stableRandom(element*31+galaxy*53)*.6)+slot*planetRadius*2.8;
}
export function systemStarOrbits(layout,scale,seed,galaxy){
 const stars=layout.filter(e=>e.rank.type.endsWith('star')),edge=12*(8.5/22)*scale*3;
 const envelopes=stars.map(star=>Math.max(scale*2.4,...layout.filter(p=>p.host===star.element).map(p=>{
  const radius=1.5*scale*p.rank.scale;
  return planetOrbitRadius(scale*2.4,radius,p.element,galaxy,p.slot)+radius*(p.rank.type==='ring-planet'?2.25:1.055);
 })));
 const base=stars.map((_,i)=>Math.max(2.5*edge+scale*2.4,edge+envelopes[i]+scale*.6));
 const count=stars.length,band=Math.max(scale*(2.5*Math.sqrt(Math.max(0,count-1))+Math.max(0,count-1)*.55),(envelopes.reduce((a,b)=>a+b,0)/Math.max(1,count))*Math.sqrt(Math.max(0,count-1))*1.2),placed=[];
 return stars.map((star,i)=>{
  const m=starMotion(seed+i*137),u=(i+.3*stableRandom(seed+i*53))/Math.max(1,count-1);
  m.radius=base[i]+band*u;
  m.phase=i*2.3999632297+stableRandom(seed)*Math.PI*2;
  if(count>=16){const arm=i%3,v=Math.floor(i/3)/Math.max(1,Math.ceil(count/3)-1);m.phase=[.15,2.35,4.6][arm]+v*[1.7,.95,.65][arm];m.radius=base[i]+band*(.08+v*[1,.7,.85][arm]);}
  for(let attempt=0;attempt<400;attempt++){
   const x=Math.cos(m.phase)*m.radius,z=Math.sin(m.phase)*m.radius;
   if(placed.every((p,j)=>Math.hypot(x-p.x,z-p.z)>=Math.max(scale*6,(envelopes[i]+envelopes[j])*.65))){placed.push({x,z});break;}
   m.phase+=.19;if(attempt%24===23)m.radius+=scale*2;
  }
  m.orbit=2*Math.PI/(22+Math.min(...base)*2);m.inclination=0;
  return m;
 });
}
