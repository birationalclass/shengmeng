// Frame-time feedback, independent of viewport orientation and gameplay clocks.
export const QUALITY = [
 {id:'power',fps:30,dpr:1,pixels:1100000,dust:.55,samples:6,hole:256},
 {id:'balanced',fps:60,dpr:1.35,pixels:2000000,dust:.8,samples:10,hole:512},
 {id:'high',fps:60,dpr:1.7,pixels:3500000,dust:1,samples:16,hole:768}
];
export const MODES=['auto','high','balanced','power'];
export function renderRatio(width,height,dpr,quality){return Math.min(dpr,quality.dpr,Math.sqrt(quality.pixels/Math.max(1,width*height)));}
export class AdaptiveQuality {
 constructor({mobile=false,cores=8,mode='auto'}={}){this.level=mobile||cores<=4?1:2;this.mode=MODES.includes(mode)?mode:'auto';if(this.mode!=='auto')this.level=QUALITY.findIndex(q=>q.id===this.mode);this.reset();}
 get current(){return QUALITY[this.level];}
 reset(grace=3){this.grace=grace;this.stalls=0;this.seconds=0;this.frames=0;this.slow=0;this.fast=0;}
 setMode(mode){if(!MODES.includes(mode))return;this.mode=mode;if(mode!=='auto')this.level=QUALITY.findIndex(q=>q.id===mode);this.reset();}
 sample(dt){if(this.mode!=='auto'||dt<=0)return false;if(dt>.25){if(++this.stalls<3){this.seconds=0;this.frames=0;return false;}dt=.25;this.grace=0;}else this.stalls=0;if(this.grace>0){this.grace-=dt;return false;}
 this.seconds+=dt;this.frames++;if(this.seconds<1)return false;
 const average=this.seconds/this.frames;this.lastFrameMs=average*1000;
 this.slow=average>(this.level===0?.044:.023)?this.slow+this.seconds:0;
 this.fast=average<.0185?this.fast+this.seconds:0;this.seconds=0;this.frames=0;
 if(this.slow>=3&&this.level>0){this.level--;this.reset(5);return true;}
 if(this.fast>=30&&this.level<2){this.level++;this.reset(8);return true;}return false;
 }
}
// Capping drawing must accumulate elapsed time, not discard skipped frames.
export class RenderClock {
 constructor(){this.reset();}
 reset(){this.pending=0;this.until=0;}
 advance(dt,fps){this.pending+=dt;this.until-=dt;if(this.until>0)return 0;const elapsed=this.pending;this.pending=0;this.until=Math.max(0,this.until+1/fps);return elapsed;}
}
