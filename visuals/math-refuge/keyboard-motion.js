// Time-based velocity easing; key-repeat events never affect acceleration.
export class KeyboardMotion {
 constructor(){this.reset();}
 reset(){this.held=0;this.velocity=[0,0,0];this.turn=0;}
 update(keys,dt){
  dt=Math.max(0,Math.min(.1,dt));
  const has=(a,b)=>Number(keys.has(a)||Boolean(b&&keys.has(b)));
  const input=[has('w','arrowup')-has('s','arrowdown'),has('e','arrowright')-has('q','arrowleft'),has(' ')-has('x')];
  const length=Math.hypot(...input);
  const moving=['w','s','q','e','arrowup','arrowdown','arrowleft','arrowright',' ','x'].some(key=>keys.has(key));
  this.held=moving?this.held+dt:0;
  const t=Math.min(1,this.held/6),ramp=t*t*(3-2*t);
  const speed=keys.has('shift')?10+10*ramp:4+8*ramp;
  const weight=1-Math.exp(-dt/(length?.28:.12));
  for(let i=0;i<3;i++){this.velocity[i]+=((length?input[i]/length*speed:0)-this.velocity[i])*weight;if(!length&&Math.abs(this.velocity[i])<.001)this.velocity[i]=0;}
  const turn=(has('a')-has('d'))*.9;this.turn+=(turn-this.turn)*(1-Math.exp(-dt/.16));if(!turn&&Math.abs(this.turn)<.001)this.turn=0;
  return {forward:this.velocity[0],right:this.velocity[1],up:this.velocity[2],yaw:this.turn};
 }
}
