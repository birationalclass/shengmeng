import {BUILDING_SCALE as S,DECK_Y,HALL} from './site-layout.js';
const upper=2*DECK_Y+HALL.clearHeight/S+.20,eyeUp=upper*S+1.65,eyeDown=DECK_Y*S+1.65;
export const HALL_SLAB={min:[(HALL.west-.275)*S,(DECK_Y+HALL.clearHeight/S)*S-.25,(HALL.north-.275)*S],max:[(HALL.east+.275)*S,upper*S+.25,(HALL.south+.275)*S]};
export function slabHit(a,b){
 let enter=0,exit=1;let inside=true;
 for(let i=0;i<3;i++){
  const lo=HALL_SLAB.min[i],hi=HALL_SLAB.max[i],d=b[i]-a[i];inside&&=a[i]>lo&&a[i]<hi;
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
 const down=[...upstairs,...stairs];
 return [start,...(start[1]>end[1]?down:[...down].reverse()),end];
}
export function stopAtHallSlab(start,end){const t=slabHit(start,end);if(t===null)return end;const d=Math.hypot(...end.map((v,i)=>v-start[i])),safe=Math.max(0,t-.08/Math.max(.001,d));return start.map((v,i)=>v+(end[i]-v)*safe);}
