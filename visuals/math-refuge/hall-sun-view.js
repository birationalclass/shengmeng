import {solarState} from './solar-state.js';
import {apparentAltitude} from './solar-optics.js';
export function hallSunStart(event,date,physical=false){
 const rising=event==='sunrise';let lo=rising?0:12,hi=rising?12:24;
 for(let i=0;i<40;i++){
  const h=(lo+hi)/2,state=solarState(h,date),radius=state.radius*180/Math.PI*(physical?1:rising?3:2);
  const desired=rising?-radius-.16:radius+1;
  const above=apparentAltitude(state.elevation)>desired;
  if(above===rising)hi=h;else lo=h;
 }
 return (lo+hi)/2;
}
export const sunViewRate=seconds=>{const t=Math.min(1,Math.max(0,seconds/5));return 1+29*t*t*t*(t*(t*6-15)+10);};
