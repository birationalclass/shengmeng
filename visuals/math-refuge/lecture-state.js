export const BOARD_ORDER=[0,2,4,1,3,5];
export const PHASE_SECONDS={lift:2.6,erase:24,write:23,hold:8};
export function boardSlot(page){return BOARD_ORDER[((page%6)+6)%6];}
// Close resting seams; the two depth-separated channels still pass freely.
export const BOARD_LAYOUT={width:5.3,height:2.05,frame:.035,low:1.835,high:3.96,railBottom:.54,railTop:5.1};
export function boardHeights(mix){const {low,high}=BOARD_LAYOUT,travel=high-low;return [low+travel*mix,high-travel*mix];}
export class LectureClock{
  constructor(count){
    if(!Number.isInteger(count)||count<1)throw new Error('Lecture needs pages');
    this.count=count;this.startAt=0;this.stopAt=count-1;this.timings=new Map();this.slots=Array.from({length:6},()=>({page:-1,progress:0}));this.select(0);
  }
  select(page){
    this.page=Math.max(this.startAt,Math.min(this.stopAt,Math.trunc(page)||0));this.ended=false;this.active=boardSlot(this.page-this.startAt);
    this.phase='lift';this.elapsed=0;
  }
  seek(page){
    this.page=Math.max(this.startAt,Math.min(this.stopAt,Math.trunc(page)||0));
    this.active=boardSlot(this.page-this.startAt);this.phase='hold';this.elapsed=0;this.ended=this.page===this.stopAt;
    // Reconstruct exactly the last six pages in chronological order, never retain future ink.
    this.slots=Array.from({length:6},()=>({page:-1,progress:0}));
    for(let p=Math.max(this.startAt,this.page-5);p<=this.page;p++)this.slots[boardSlot(p-this.startAt)]={page:p,progress:1};
  }
  next(delta=1){const next=Math.max(this.startAt,Math.min(this.stopAt,this.page+delta));if(next!==this.page)this.select(next);}
  startWrite(){this.phase='write';this.elapsed=0;this.slots[this.active]={page:this.page,progress:0};}
  setDurations(page,durations){this.timings.set(page,durations);}
  get duration(){return this.timings.get(this.phase==='erase'?this.slots[this.active].page:this.page)?.[this.phase]||PHASE_SECONDS[this.phase];}
  update(dt){
    if(this.ended)return;
    this.elapsed+=Math.max(0,Math.min(dt,.1));
    if(this.phase==='write')this.slots[this.active].progress=Math.min(1,this.elapsed/this.duration);
    if(this.elapsed<this.duration)return;
    if(this.phase==='lift'){
      if(this.slots[this.active].page>=0){this.phase='erase';this.elapsed=0;}else this.startWrite();
    }else if(this.phase==='erase')this.startWrite();
    else if(this.phase==='write'){this.slots[this.active].progress=1;this.phase='hold';this.elapsed=0;this.ended=this.page===this.stopAt;}
    else this.next();
  }
  // Off-screen playback advances only this small state machine. No canvas,
  // image decoding, geometry or GPU work is needed, even after a long absence.
  advance(dt,writingSpeed=1){
    let remaining=Math.max(0,Number(dt)||0);
    while(remaining>0&&!this.ended){
      const rate=this.phase==='write'?writingSpeed:1;
      const step=Math.min(remaining,Math.max(0,this.duration-this.elapsed)/rate);
      this.elapsed+=step*rate;remaining-=step;
      if(this.phase==='write')this.slots[this.active].progress=Math.min(1,this.elapsed/this.duration);
      if(this.elapsed+1e-8<this.duration)break;
      if(this.phase==='lift'){
        if(this.slots[this.active].page>=0){this.phase='erase';this.elapsed=0;}else this.startWrite();
      }else if(this.phase==='erase')this.startWrite();
      else if(this.phase==='write'){this.slots[this.active].progress=1;this.phase='hold';this.elapsed=0;this.ended=this.page===this.stopAt;}
      else this.next();
    }
  }
  get progress(){return Math.min(1,this.elapsed/this.duration);}
}
