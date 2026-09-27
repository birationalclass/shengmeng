import {fromBeach,COAST_LIFT} from './elliptic-site.js';
// Above the left ring, eastward (+X) and downward toward the main hall.
const [x,z]=fromBeach(-1000,0);
export const OPENING_POSE={position:[x,450+COAST_LIFT,z],target:[x+1500,2.55+COAST_LIFT,z],fov:64};
export class OpeningCameraLock{
 constructor(){this.until=0;}
 start(now){this.until=now+10000;}
 remaining(now){return Math.max(0,Math.ceil((this.until-now)/1000));}
 locked(now){return this.remaining(now)>0;}
}

// Match the 1280x720 first-frame poster's object-fit:cover crop exactly.
export function openingFrameFov(aspect){
 const verticalScale=Math.min(1,(1280/720)/Math.max(.01,aspect));
 return 2*Math.atan(Math.tan(OPENING_POSE.fov*Math.PI/360)*verticalScale)*180/Math.PI;
}
