// Retain the whole flight, including stalls that a rolling FPS window would hide.
export class OpeningPerformance {
 constructor(){this.frames=[];this.cpu=[];this.phase='idle';this.duration=0;}
 start(now){this.frames=[];this.cpu=[];this.startAt=now;this.phase='moving';}
 sample(frameMs,cpuMs){if(this.phase!=='moving'||frameMs<=0)return;this.frames.push(frameMs);this.cpu.push(cpuMs);}
 finish(now){this.duration=now-this.startAt;this.phase='complete';return this.snapshot();}
 snapshot(){const f=[...this.frames].sort((a,b)=>a-b),c=[...this.cpu].sort((a,b)=>a-b),p=(a,q)=>a.length?a[Math.min(a.length-1,Math.floor(a.length*q))]:0;return {phase:this.phase,frames:f.length,durationMs:Math.round(this.duration),frameP50:p(f,.5),frameP95:p(f,.95),frameP99:p(f,.99),maxFrameMs:p(f,1),over50ms:f.filter(v=>v>50).length,over100ms:f.filter(v=>v>100).length,cpuP95:p(c,.95)};}
}
