export const wrapHour=h=>((Number(h)||0)%24+24)%24;
export function daylightAt(hour){return Math.max(0,Math.sin((wrapHour(hour)-6)*Math.PI/12));}
export class RetreatTime{
  constructor(){this.hour=8;this.running=true;}
  update(dt,reduced=false){if(this.running&&!reduced)this.hour=wrapHour(this.hour+Math.max(0,dt)*24/600);return this.hour;}
}
