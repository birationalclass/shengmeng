// Approach at real-time speed, then ease into accelerated dawn after arrival.
export class SunriseIntro {
 constructor(clock,presentation){this.clock=clock;this.presentation=presentation;this.active=false;this.waiting=false;this.catchingUp=false;this.elapsed=0;this.catchElapsed=0;}
 prepare(sunrise){this.elapsed=0;this.active=false;this.catchingUp=false;this.waiting=true;this.clock.previewAt(sunrise-.10);this.clock.play(1);this.presentation.hour=this.clock.hour;}
 arrive(){if(!this.waiting)return;this.waiting=false;this.active=true;this.clock.play(1);}
 start(sunrise){this.prepare(sunrise);this.arrive();}
 cancel(){this.active=false;this.waiting=false;if(this.catchingUp)this.clock.setRate(1);this.catchingUp=false;}
 update(dt){
  dt=Math.max(0,dt);
  if(this.active){this.elapsed+=dt;const ramp=Math.min(1,this.elapsed/5);this.clock.rate=1+29*ramp*ramp*(3-2*ramp);if(this.elapsed>=30){this.active=false;this.catchingUp=true;this.catchElapsed=0;}return false;}
  if(!this.catchingUp)return false;
  const real=this.clock.hourOf(this.clock.now()),remaining=((real-this.clock.hour+24)%24)*3600;
  if(remaining<.25+dt||remaining>86400-(.25+dt)){this.catchingUp=false;this.clock.setRate(1);this.clock.sync();return true;}
  this.catchElapsed+=dt;const t=Math.min(1,this.catchElapsed/3),ease=t*t*(3-2*t);
  // Start at the existing 30x, reach 1500x smoothly, then brake near real time.
  const accelerated=30+1470*ease,braking=1+Math.sqrt(150*remaining);
  this.clock.rate=Math.min(1500,accelerated,braking,remaining/Math.max(.001,dt));
  return false;
 }
}
