export const wrapHour=h=>((Number(h)||0)%24+24)%24;
export function daylightAt(hour){return Math.max(0,Math.sin((wrapHour(hour)-6)*Math.PI/12));}
export const localHour=date=>date.getHours()+date.getMinutes()/60+date.getSeconds()/3600+date.getMilliseconds()/3600000;
export class RetreatTime{
  constructor(now=()=>new Date(),hourOf=localHour){this.now=now;this.hourOf=hourOf;this.preview=false;this.playing=false;this.rate=1;this.hour=this.hourOf(this.now());}
  update(dt=0){if(!this.preview)this.hour=this.hourOf(this.now());else if(this.playing)this.hour=wrapHour(this.hour+Math.max(0,dt)*this.rate/3600);return this.hour;}
  previewAt(hour){this.playing=false;this.preview=true;this.hour=wrapHour(hour);return this.hour;}
  setRate(rate){this.rate=Math.max(1,Math.min(60,Number(rate)||1));}
  play(rate=this.rate){this.update();this.setRate(rate);this.preview=true;this.playing=true;}
  pause(){this.update();this.preview=true;this.playing=false;}
  sync(){this.playing=false;this.preview=false;return this.update();}
}
