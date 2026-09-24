// Artistic bathymetry in metres; inputs are site-plan coordinates, not world metres.
// Two independent shelves keep the kilometre-wide channel between inhabited islands deep.
import {BUILDING_SCALE as S} from './site-layout.js';
import {RESIDENCE} from './residence-layout.js';
const smooth=(a,b,x)=>{const t=Math.max(0,Math.min(1,(x-a)/(b-a)));return t*t*(3-2*t);};
const villa=[RESIDENCE.origin[0]/S,RESIDENCE.origin[2]/S,(RESIDENCE.halfWidth+8)/S,(RESIDENCE.halfDepth+8)/S];
export function seaDepthAt(x,z){
 const campus=Math.hypot(Math.max(Math.abs(x+20.5)-74.5,0),Math.max(Math.abs(z+6)-49,0));
 const residence=(Math.hypot((x-villa[0])/villa[2],(z-villa[1])/villa[3])-1)*villa[3];
 const distance=Math.max(0,Math.min(campus,residence));
 const shallows=1.5+.7*(.5+.5*Math.sin(x*.047+z*.029))+.8*smooth(0,22,distance);
 return shallows+(88-shallows)*smooth(22,205,distance);
}
// Generate geographic constants from the same layout data used by the CPU model.
const f=n=>Number(n).toFixed(9);
export const seaDepthGLSL=`float seaDepthAt(vec2 p){
 float campus=length(max(abs(p+vec2(20.5,6.0))-vec2(74.5,49.0),vec2(0.0)));
 float residence=(length((p-vec2(${f(villa[0])},${f(villa[1])}))/vec2(${f(villa[2])},${f(villa[3])}))-1.0)*${f(villa[3])};
 float distance=max(0.0,min(campus,residence));
 float shallows=1.5+.7*(.5+.5*sin(p.x*.047+p.y*.029))+.8*smoothstep(0.0,22.0,distance);
 return mix(shallows,88.0,smoothstep(22.0,205.0,distance));
}`;
