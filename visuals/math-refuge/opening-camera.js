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
