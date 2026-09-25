import {fromBeach,COAST_LIFT} from './elliptic-site.js';
// Above the left ring, eastward (+X) and downward toward the main hall.
const [x,z]=fromBeach(0,0);
export const OPENING_POSE={position:[x,900+COAST_LIFT,z],target:[x+2000,80+COAST_LIFT,z],fov:64};
export class OpeningCameraLock{
 constructor(){this.until=0;}
 start(now){this.until=now+30000;}
 remaining(now){return Math.max(0,Math.ceil((this.until-now)/1000));}
 locked(now){return this.remaining(now)>0;}
}
