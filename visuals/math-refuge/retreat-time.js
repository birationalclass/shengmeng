export const wrapHour=h=>((Number(h)||0)%24+24)%24;
export function daylightAt(hour){return Math.max(0,Math.sin((wrapHour(hour)-6)*Math.PI/12));}
export function roofTarget(hour,mode='auto'){return mode==='open'?1:mode==='closed'?0:(wrapHour(hour)>=6&&wrapHour(hour)<18?0:1);}
export class RetreatTime{
  constructor(){this.hour=8;this.running=true;this.mode='auto';this.open=0;}
  update(dt,reduced=false){
    if(this.running&&!reduced)this.hour=wrapHour(this.hour+Math.max(0,dt)*24/600);
    const target=roofTarget(this.hour,this.mode);
    this.open=reduced?target:this.open+(target-this.open)*(1-Math.exp(-Math.max(0,dt)*.8));
    if(Math.abs(this.open-target)<.0001)this.open=target;
    return this.open;
  }
}
