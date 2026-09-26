import {buildingOffset} from './campus-layout.js';
const hallOffset=buildingOffset('01B');
import {BUILDING_SCALE as S,DECK_Y,HALL} from './site-layout.js';
const upper=2*DECK_Y+HALL.clearHeight/S+.20,eyeUp=upper*S+1.65,eyeDown=DECK_Y*S+1.65;
export const HALL_SLAB={min:[(HALL.west-.275)*S,(DECK_Y+HALL.clearHeight/S)*S-.25,(HALL.north-.275)*S],max:[(HALL.east+.275)*S,upper*S+.25,(HALL.south+.275)*S]};
for(const p of [HALL_SLAB.min,HALL_SLAB.max]){p[0]+=hallOffset.x;p[2]+=hallOffset.z;}
export function slabHit(a,b,radius=0){
 let enter=0,exit=1;let inside=true;
 for(let i=0;i<3;i++){
  const lo=HALL_SLAB.min[i]-radius,hi=HALL_SLAB.max[i]+radius,d=b[i]-a[i];inside&&=a[i]>lo&&a[i]<hi;
  if(Math.abs(d)<1e-9){if(a[i]<lo||a[i]>hi)return null;continue;}
  const t0=(lo-a[i])/d,t1=(hi-a[i])/d;enter=Math.max(enter,Math.min(t0,t1));exit=Math.min(exit,Math.max(t0,t1));if(enter>exit)return null;
 }
 return inside||exit<0||enter>1?null:Math.max(0,enter);
}
export function hallFloorRoute(start,end){
 // Only a transition crossing this slab is rerouted; ordinary observation is unchanged.
 if(slabHit(start,end)===null||Math.max(start[1],end[1])>eyeUp+1)return null;
 const x=(HALL.west-1.5)*S;
 const upstairs=[ [37.4*S,eyeUp,0],[34.8*S,eyeUp,0],[x,eyeUp,0],[x,eyeUp,1.32*S] ];
 const stairs=[[x,eyeDown,9.6*S],[x,eyeDown,0],[35.3*S,eyeDown,0]];
 const down=[...upstairs,...stairs].map(p=>[p[0]+hallOffset.x,p[1],p[2]+hallOffset.z]);
 return [start,...(start[1]>end[1]?down:[...down].reverse()),end];
}
export function stopAtHallSlab(start,end){const t=slabHit(start,end);if(t===null)return end;const d=Math.hypot(...end.map((v,i)=>v-start[i])),safe=Math.max(0,t-.08/Math.max(.001,d));return start.map((v,i)=>v+(end[i]-v)*safe);}

// A conservative sphere encloses the near plane even at wide aspect ratios.
export function cameraProbeRadius(near=.1,fov=60,aspect=16/9){
 const h=near*Math.tan(fov*Math.PI/360);
 return Math.max(.14,Math.hypot(near,h,h*aspect)+.04);
}
export function slabClearance(p){
 return Math.hypot(...p.map((v,i)=>Math.max(HALL_SLAB.min[i]-v,0,v-HALL_SLAB.max[i])));
}
export function curveClearsHall(curve,radius=.18){
 const steps=Math.max(64,Math.ceil(curve.getLength()/.10));let prior=curve.getPointAt(0).toArray();
 for(let i=0;i<=steps;i++){const next=curve.getPointAt(i/steps).toArray();if(slabClearance(next)<radius||slabHit(prior,next,radius)!==null)return false;prior=next;}
 return true;
}
// Manual free-flight remains free: mask a forced passage rather than clamping floors.
export class HallPassageMask{
 constructor(){this.opacity=0;this.hold=0;}
 update(start,end,radius,dt){
  const clearance=Math.min(slabClearance(start),slabClearance(end));
  const crossing=slabHit(start,end,radius)!==null;
  const t=Math.max(0,Math.min(1,(clearance-radius)/.55));
  const desired=1-t*t*(3-2*t);
  if(crossing)this.hold=.10;else this.hold=Math.max(0,this.hold-dt);
  const target=this.hold>0?1:desired;
  // Immediate protection, damped recovery, no oscillating positional correction.
  this.opacity=target>this.opacity?target:Math.max(target,this.opacity-dt/ .28);
  return this.opacity;
 }
}
