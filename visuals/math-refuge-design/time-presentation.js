// Seek under a short fade, never animate the Sun backward around the clock.
export class TimePresentation {
 constructor(hour){this.hour=hour;this.phase='idle';this.progress=0;this.opacity=0;}
 seek(){if(this.phase!=='out'){this.phase='out';this.progress=this.opacity*.18;}}
 update(target,dt){
  const step=Math.max(0,Math.min(.1,dt));
  if(this.phase==='out'){this.progress+=step;this.opacity=Math.min(1,this.progress/.18);if(this.opacity===1){this.hour=target;this.phase='in';this.progress=0;}}
  else {this.hour=target;if(this.phase==='in'){this.progress+=step;this.opacity=Math.max(0,1-this.progress/.24);if(this.opacity===0)this.phase='idle';}}
  return this.hour;
 }
}
