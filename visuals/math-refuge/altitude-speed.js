// Height is measured in metres above the current sea surface.
export function horizontalSpeedLimit(height=0){
 const t=Math.max(0,Math.min(1,((Number.isFinite(height)?height:0)-10)/990));
 return 100+300*t*t*(3-2*t);
}
export class AltitudeDialRange{
 constructor(){this.upper=100;this.displayUpper=100;}
 update(limit,dt){
  limit=Math.max(100,Math.min(400,limit));
  while(limit>this.upper&&this.upper<400)this.upper+=50;
  while(this.upper>100&&limit<this.upper-55)this.upper-=50;
  if(limit===100)this.upper=100;
  this.displayUpper+=(this.upper-this.displayUpper)*(1-Math.exp(-Math.max(0,dt)/.55));
  return {max:this.upper,min:this.upper-100,displayMax:this.displayUpper,displayMin:this.displayUpper-100};
 }
}
