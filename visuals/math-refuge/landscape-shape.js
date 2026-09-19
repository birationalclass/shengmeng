// Deterministic continuous terrain shared by geometry, planting and shoreline.
export const seaLevel=-9;
const mix=(a,b,t)=>a+(b-a)*t;
const smooth=(a,b,x)=>{const t=Math.max(0,Math.min(1,(x-a)/(b-a)));return t*t*(3-2*t);};
const hash=(x,z)=>{const n=Math.sin(x*127.1+z*311.7)*43758.5453;return n-Math.floor(n);};
export function noise(x,z){
  const ix=Math.floor(x),iz=Math.floor(z),u=smooth(0,1,x-ix),v=smooth(0,1,z-iz);
  return mix(mix(hash(ix,iz),hash(ix+1,iz),u),mix(hash(ix,iz+1),hash(ix+1,iz+1),u),v);
}
export function fractal(x,z){
  let n=0,a=.55;
  for(let i=0;i<5;i++){n+=noise(x,z)*a;x=x*2.07+13.7;z=z*2.03-9.2;a*=.48;}
  return n;
}
export const coastline=z=>49+Math.sin(z*.022)*5+Math.sin(z*.081)*2;
export function elevation(x,z){
  const west=smooth(35,260,-x),north=smooth(42,290,-z);
  const ridge=1-Math.abs(2*noise(x*.011+5,z*.009)-1);
  const mountains=(west*.85+north*.7)*(28+fractal(x*.006,z*.006)*120+ridge*ridge*45);
  const raw=-3+fractal(x*.029,z*.029)*9+mountains;
  const foundation=smooth(1,1.5,Math.max(Math.abs(x-10)/34,Math.abs(z)/20));
  const land=mix(-2.1,raw,foundation);
  const cliff=smooth(coastline(z)-4,coastline(z)+11,x);
  return mix(land,-22,cliff);
}
export function slope(x,z){return Math.hypot(elevation(x+.5,z)-elevation(x-.5,z),elevation(x,z+.5)-elevation(x,z-.5));}
export function canPlant(x,z){
  return x<coastline(z)-9 && !(x>-21&&x<53&&Math.abs(z)<22) && slope(x,z)<1.25 && elevation(x,z)>seaLevel+3;
}
export function shoreline(z){
  let a=coastline(z)-4,b=coastline(z)+11;
  for(let i=0;i<22;i++){const mid=(a+b)/2;if(elevation(mid,z)>seaLevel)a=mid;else b=mid;}
  return (a+b)/2;
}
export function seededRandom(seed){return ()=>{seed=(seed*1664525+1013904223)>>>0;return seed/4294967296;};}
