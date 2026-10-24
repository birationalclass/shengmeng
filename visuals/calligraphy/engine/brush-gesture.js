import {profile} from './stroke-volume.js';

const clamp=(v,a=0,b=1)=>Math.max(a,Math.min(b,v));
const smooth=v=>{v=clamp(v);return v*v*v*(10+v*(-15+6*v));};

// Monotone cubic time-to-distance curve. A turn can dwell while the thin
// descending run accelerates; the finished contour is unchanged by its clock.
export function writingProgress(spec,time,mode='flow'){
 const keys=mode==='flow'&&!spec.forceReveal&&spec.gesture?.timing;
 if(!keys)return profile(spec.motion||[0,1],time);
 const t=clamp(time),slopes=keys.slice(1).map((q,i)=>(q[1]-keys[i][1])/(q[0]-keys[i][0]));
 let i=0;while(i<keys.length-2&&keys[i+1][0]<t)i++;
 const tangent=j=>j===0?slopes[0]:j===keys.length-1?slopes.at(-1):slopes[j-1]*slopes[j]<=0?0:2/(1/slopes[j-1]+1/slopes[j]);
 const a=keys[i],b=keys[i+1],h=b[0]-a[0],u=clamp((t-a[0])/h),v=u*u,w=v*u;
 return clamp((2*w-3*v+1)*a[1]+(w-2*v+u)*h*tangent(i)+(-2*w+3*v)*b[1]+(w-v)*h*tangent(i+1),a[1],b[1]);
}

// Only the travelling, still-forming end changes. The settled body stays on
// its authored rails. The leading edge arrives first, then the broad face
// opens behind it, with a local roll and pressure-dependent section.
export function brushHead(spec,progress,u,mode='flow',motion){
 const g=mode==='flow'&&spec.gesture;if(!g)return {spread:1,pressure:1,shift:0,roll:0};
 const settle=1-smooth((progress-.87)/.13),wake=(g.wake||.10)*settle;
 const mature=wake>1e-7?smooth((progress-u)/wake):1,active=1-mature;
 let turnWeight=0;if(g.continuous)for(const joint of g.turns||[])turnWeight=Math.max(turnWeight,1-smooth((Math.abs(progress-joint)-.02)/.08));
 const leadingSpread=g.continuous?.32+.58*turnWeight:.10;
 return {spread:leadingSpread+(1-leadingSpread)*mature,pressure:1+active*((motion?.pressure??profile(g.pressure||[.6,1,.3],progress))-1),shift:(g.leadingEdge||0)*active*.5,roll:(motion?.roll??profile(g.roll||[0,0],progress))*active*settle};
}

export function writingPhase(spec,progress){
 const phases=spec.gesture?.phases||[];let label='';for(const [at,text] of phases){if(progress<at)break;label=text;}return label;
}
