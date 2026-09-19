// Deterministic continuous terrain shared by geometry, planting and shoreline.
import {watercourse,ROOM_PADS,inBuilding,inPool} from './site-layout.js?v=9-peninsula';
export const seaLevel=-3;
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
// A single west-connected peninsula. The coast recedes rapidly westwards to
// the north and south; no terrain remains across the east-facing sea horizon.
export const coastline=z=>27-25*Math.pow(Math.abs(z)/38,4);
export function elevation(x,z){
  const west=smooth(65,260,-x);
  const ridge=1-Math.abs(2*noise(x*.011+5,z*.009)-1);
  const mountains=west*(28+fractal(x*.006,z*.006)*120+ridge*ridge*45);
  const raw=-3+fractal(x*.029,z*.029)*9+mountains;
  let foundation=smooth(1,1.35,Math.max(Math.abs(x-2)/26,Math.abs(z)/24));
  for(const [a,b,c,d] of ROOM_PADS){const dx=Math.max(a-x,0,x-b),dz=Math.max(c-z,0,z-d);foundation=Math.min(foundation,smooth(1,6,Math.hypot(dx,dz)));}
  const land=mix(-1.1,raw,foundation);
  const cliff=smooth(coastline(z)-2,coastline(z)+7,x);
  const base=mix(land,-15,cliff),river=watercourse(x,z);
  const valley=1-smooth(river.width*.86,river.width+3.1,river.distance);
  return Math.min(base,mix(base,river.y-.85,valley));
}
export function slope(x,z){return Math.hypot(elevation(x+.5,z)-elevation(x-.5,z),elevation(x,z+.5)-elevation(x,z-.5));}
export function canPlant(x,z){
  const river=watercourse(x,z);
  return river.distance>river.width+1.8&&x<coastline(z)-5&&!inBuilding(x,z,3)&&!inPool(x,z,3)&&!(x>-56&&x<25&&z>5&&z<11)&&slope(x,z)<1.25&&elevation(x,z)>seaLevel+1;
}
export function shoreline(z){
  let a=coastline(z)-2,b=coastline(z)+7;
  for(let i=0;i<22;i++){const mid=(a+b)/2;if(elevation(mid,z)>seaLevel)a=mid;else b=mid;}
  return (a+b)/2;
}
export function seededRandom(seed){return ()=>{seed=(seed*1664525+1013904223)>>>0;return seed/4294967296;};}
