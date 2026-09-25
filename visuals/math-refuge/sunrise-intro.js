// Opening owns time only until the visitor changes a time control.
export class SunriseIntro {
 constructor(clock,presentation){this.clock=clock;this.presentation=presentation;this.active=false;this.elapsed=0;}
 start(sunrise){this.elapsed=0;this.active=true;this.clock.previewAt(sunrise-.025);this.clock.play(30);this.presentation.hour=this.clock.hour;}
 cancel(){this.active=false;}
 update(dt){if(!this.active)return;this.elapsed+=Math.max(0,dt);if(this.elapsed>=30){this.active=false;this.presentation.seek();this.clock.sync();}}
}
