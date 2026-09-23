export const wrapHour=h=>((Number(h)||0)%24+24)%24;
export function daylightAt(hour){return Math.max(0,Math.sin((wrapHour(hour)-6)*Math.PI/12));}
export const localHour=date=>date.getHours()+date.getMinutes()/60+date.getSeconds()/3600+date.getMilliseconds()/3600000;
export class RetreatTime{
  constructor(now=()=>new Date(),hourOf=localHour){this.now=now;this.hourOf=hourOf;this.preview=false;this.hour=this.hourOf(this.now());}
  update(){if(!this.preview)this.hour=this.hourOf(this.now());return this.hour;}
  previewAt(hour){this.preview=true;this.hour=wrapHour(hour);return this.hour;}
  sync(){this.preview=false;return this.update();}
}
