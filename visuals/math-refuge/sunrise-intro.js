// Hold dawn during the opening camera move; count playback only after arrival.
export class SunriseIntro {
 constructor(clock,presentation){this.clock=clock;this.presentation=presentation;this.active=false;this.waiting=false;this.elapsed=0;}
 prepare(sunrise){this.elapsed=0;this.active=false;this.waiting=true;this.clock.previewAt(sunrise-.025);this.clock.setRate(30);this.presentation.hour=this.clock.hour;}
 arrive(){if(!this.waiting)return;this.waiting=false;this.active=true;this.clock.play(30);}
 start(sunrise){this.prepare(sunrise);this.arrive();}
 cancel(){this.active=false;this.waiting=false;}
 update(dt){if(!this.active)return false;this.elapsed+=Math.max(0,dt);if(this.elapsed>=30){this.active=false;this.presentation.seek();this.clock.setRate(1);this.clock.sync();return true;}return false;}
}
