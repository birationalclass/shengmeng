// Count actual active teaching time, including physical board holds; manual pause freezes it.
export class LessonBudget{
 constructor(){this.select(null);}
 select(id){this.id=id;this.period=0;this.elapsed=0;this.decision=null;}
 configure(manifest){this.secondStart=manifest?.periods?.find(p=>p.id===2)?.start??3000;this.finish=manifest?.duration??5700;}
 seek(time,optional=[]){this.period=time>=(this.secondStart??3000)?2:1;this.elapsed=Math.max(0,time-(this.period===2?(this.secondStart??3000):0));this.decision=optional.some(b=>time>=b.start&&time<b.end)?'full':null;}
 advance(dt,{started,time,transportPlaying}){if(this.id!=='sylow-theorems'||!started)return;const period=time>=(this.secondStart??3000)?2:1;if(period!==this.period){this.period=period;this.elapsed=0;this.decision=null;}if(transportPlaying)this.elapsed+=Math.max(0,dt);}
 shouldSkip(board,optional){if(this.id!=='sylow-theorems'||this.period!==2||this.decision||!optional.length||board?.page!==optional[0].page)return false;const needed=(this.finish??5700)-optional[0].start;this.decision=this.elapsed+needed>2700?'skip':'full';return this.decision==='skip';}
}
