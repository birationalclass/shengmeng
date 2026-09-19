// Open-ocean site: no above-water terrain or natural shore vegetation.
import {inBuilding,inPool,inGarden} from './site-layout.js?v=11-open-sea';
export const seaLevel=-.25;
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
// Compatibility sentinel outside the modeled world; no coast mesh is created.
export const coastline=()=>-100000;
export function elevation(){return -15;}
export function slope(x,z){return Math.hypot(elevation(x+.5,z)-elevation(x-.5,z),elevation(x,z+.5)-elevation(x,z-.5));}
export const gardenElevation=(x,z)=>inGarden(x,z) ? .24 : elevation(x,z);
export const canGardenPlant=(x,z)=>inGarden(x,z)&&!inBuilding(x,z,.5)&&!inPool(x,z,.5)&&!(z>6.5&&z<9.5);
export const canPlant=()=>false;
export const shoreline=()=>null;
export function seededRandom(seed){return ()=>{seed=(seed*1664525+1013904223)>>>0;return seed/4294967296;};}
