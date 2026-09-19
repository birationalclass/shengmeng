export const BOARD_ORDER=[0,2,4,1,3,5];
export const PHASE_SECONDS={lift:2.6,erase:24,write:23,hold:8};
export function boardSlot(page){return BOARD_ORDER[((page%6)+6)%6];}
export function boardHeights(mix){return [1.45+2.25*mix,3.7-2.25*mix];}
export class LectureClock{
  constructor(count){
    if(!Number.isInteger(count)||count<1)throw new Error('Lecture needs pages');
    this.count=count;this.slots=Array.from({length:6},()=>({page:-1,progress:0}));this.select(0);
  }
  select(page){
    this.page=((page%this.count)+this.count)%this.count;this.active=boardSlot(this.page);
    this.phase='lift';this.elapsed=0;
  }
  next(delta=1){this.select(this.page+delta);}
  startWrite(){this.phase='write';this.elapsed=0;this.slots[this.active]={page:this.page,progress:0};}
  update(dt){
    this.elapsed+=Math.max(0,Math.min(dt,.1));
    if(this.phase==='write')this.slots[this.active].progress=Math.min(1,this.elapsed/PHASE_SECONDS.write);
    if(this.elapsed<PHASE_SECONDS[this.phase])return;
    if(this.phase==='lift'){
      if(this.slots[this.active].page>=0){this.phase='erase';this.elapsed=0;}else this.startWrite();
    }else if(this.phase==='erase')this.startWrite();
    else if(this.phase==='write'){this.slots[this.active].progress=1;this.phase='hold';this.elapsed=0;}
    else this.next();
  }
  get progress(){return Math.min(1,this.elapsed/PHASE_SECONDS[this.phase]);}
}
