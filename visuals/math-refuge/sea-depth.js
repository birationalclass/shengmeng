// Artistic bathymetry in metres; inputs are site-plan coordinates, not world metres.
// Two independent shelves keep the kilometre-wide channel between inhabited islands deep.
import {BUILDING_SCALE as S} from './site-layout.js';
import {RESIDENCE} from './residence-layout.js';
const smooth=(a,b,x)=>{const t=Math.max(0,Math.min(1,(x-a)/(b-a)));return t*t*(3-2*t);};
const villa=[RESIDENCE.origin[0]/S,RESIDENCE.origin[2]/S,(RESIDENCE.halfWidth+8)/S,(RESIDENCE.halfDepth+8)/S];
export function terraceDistance(x,z){const dx=Math.abs(x-39)-15,dz=Math.abs(z)-16.5;return Math.hypot(Math.max(dx,0),Math.max(dz,0))+Math.min(Math.max(dx,dz),0);}
const hash=(x,z)=>{const n=Math.sin(x*127.1+z*311.7)*43758.5453;return n-Math.floor(n);};
const noise=(x,z)=>{const i=Math.floor(x),j=Math.floor(z),u=smooth(0,1,x-i),v=smooth(0,1,z-j);return (hash(i,j)*(1-u)+hash(i+1,j)*u)*(1-v)+(hash(i,j+1)*(1-u)+hash(i+1,j+1)*u)*v;};
const beachWidth=(x,z)=>10+8*smooth(30,54,x)+4*smooth(-10,20,z)+10*(noise(x*.12,z*.12)-.5)+5*(noise(x*.31+4,z*.31-3)-.5)+1*(noise(x*.41,z*.41)-.5);
const beachSides=(x,z)=>1-(1-smooth(48,54,x)*smooth(-25,-20,z))*(1-smooth(10.5,16.5,z)*smooth(24,32,x))*(1-smooth(46,53,x)*(1-smooth(-17,-12,z)));
export function beachMask(x,z){const d=terraceDistance(x,z);return beachSides(x,z)*smooth(-1.2,-.15,d)*(1-smooth(beachWidth(x,z)*.3,beachWidth(x,z)*1.8,d));}
export function beachDepth(x,z){const d=Math.max(0,terraceDistance(x,z))*17/beachWidth(x,z);return -.65*S+2.25*smooth(0,13,d)+.18*(noise(x*1.1,z*1.1)-.5)*smooth(.5,2,d)*(1-smooth(5,9,d));}
export function seaDepthAt(x,z){
 const campus=Math.hypot(Math.max(Math.abs(x+20.5)-74.5,0),Math.max(Math.abs(z+6)-49,0));
 const residence=(Math.hypot((x-villa[0])/villa[2],(z-villa[1])/villa[3])-1)*villa[3];
 const distance=Math.max(0,Math.min(campus,residence));
 const shallows=1.5+.7*(.5+.5*Math.sin(x*.047+z*.029))+.8*smooth(0,22,distance);
 const base=shallows+(88-shallows)*smooth(22,205,distance);return base+(beachDepth(x,z)-base)*beachMask(x,z);
}
// Generate geographic constants from the same layout data used by the CPU model.
const f=n=>Number(n).toFixed(9);
export const seaDepthGLSL=`float terraceDistance(vec2 p){vec2 q=abs(p-vec2(39.,0.))-vec2(15.,16.5);return length(max(q,vec2(0.)))+min(max(q.x,q.y),0.);}
float coastHash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7)))*43758.5453);}
float coastNoise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(coastHash(i),coastHash(i+vec2(1,0)),f.x),mix(coastHash(i+vec2(0,1)),coastHash(i+vec2(1,1)),f.x),f.y);}
float beachWidth(vec2 p){return 10.+8.*smoothstep(30.,54.,p.x)+4.*smoothstep(-10.,20.,p.y)+10.*(coastNoise(p*.12)-.5)+5.*(coastNoise(p*.31+vec2(4,-3))-.5)+1.*(coastNoise(p*.41)-.5);}
float beachMask(vec2 p){float d=terraceDistance(p),w=beachWidth(p);float sides=1.-(1.-smoothstep(48.,54.,p.x)*smoothstep(-25.,-20.,p.y))*(1.-smoothstep(10.5,16.5,p.y)*smoothstep(24.,32.,p.x))*(1.-smoothstep(46.,53.,p.x)*(1.-smoothstep(-17.,-12.,p.y)));return sides*smoothstep(-1.2,-.15,d)*(1.-smoothstep(w*.3,w*1.8,d));}
float beachDepth(vec2 p){float w=beachWidth(p),d=max(0.,terraceDistance(p))*17./w;return -${f(.65*S)}+2.25*smoothstep(0.,13.,d)+.18*(coastNoise(p*1.1)-.5)*smoothstep(.5,2.,d)*(1.-smoothstep(5.,9.,d));}
float seaDepthAt(vec2 p){
 float campus=length(max(abs(p+vec2(20.5,6.0))-vec2(74.5,49.0),vec2(0.0)));
 float residence=(length((p-vec2(${f(villa[0])},${f(villa[1])}))/vec2(${f(villa[2])},${f(villa[3])}))-1.0)*${f(villa[3])};
 float distance=max(0.0,min(campus,residence));
 float shallows=1.5+.7*(.5+.5*sin(p.x*.047+p.y*.029))+.8*smoothstep(0.0,22.0,distance);
 return mix(mix(shallows,88.0,smoothstep(22.0,205.0,distance)),beachDepth(p),beachMask(p));
}`;
