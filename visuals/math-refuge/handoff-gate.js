// A handoff ends playback until the teacher explicitly resumes. Seeking is an
// explicit navigation action; replaying from before a cue arms it again.
export class HandoffGate{
 constructor(){this.reset();}
 reset(cues=[],at=0){this.cues=[...cues].sort((a,b)=>a.at-b.at);this.seek(at);}
 seek(at){this.previous=Math.max(0,Number(at)||0);this.fired=new Set(this.cues.filter(c=>c.at<=this.previous+.001).map(c=>c.id));}
 check(at,playing){at=Math.max(0,Number(at)||0);if(at<this.previous-.03)this.seek(at);if(!playing)return null;const cue=this.cues.find(c=>!this.fired.has(c.id)&&c.at>=this.previous-.001&&c.at<=at+.001);this.previous=cue?cue.at:at;if(cue)this.fired.add(cue.id);return cue||null;}
}
