// Count actual active teaching time, including physical board holds; manual pause freezes it.
export class LessonBudget{
 constructor(){this.select(null);}
 select(id){this.id=id;this.period=0;this.elapsed=0;this.decision=null;}
 seek(time,optional=[]){this.period=time>=3000?2:1;this.elapsed=Math.max(0,time-(this.period===2?3000:0));this.decision=optional.some(b=>time>=b.start&&time<b.end)?'full':null;}
 advance(dt,{started,time,transportPlaying}){if(this.id!=='sylow-theorems'||!started)return;const period=time>=3000?2:1;if(period!==this.period){this.period=period;this.elapsed=0;this.decision=null;}if(transportPlaying)this.elapsed+=Math.max(0,dt);}
 shouldSkip(board,optional){if(this.id!=='sylow-theorems'||this.period!==2||this.decision||!optional.length||board?.page!==optional[0].page)return false;this.decision=this.elapsed>optional[0].start-3000+1?'skip':'full';return this.decision==='skip';}
}
