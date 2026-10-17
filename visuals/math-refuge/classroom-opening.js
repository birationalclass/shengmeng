// Choose a real recorded greeting using the playback device's local clock.
export function openingPeriod(date=new Date()){
 const hour=date.getHours();return hour<12?'morning':hour<18?'afternoon':'evening';
}
export function selectClassroomOpening(source,date=new Date()){
 const period=openingPeriod(date),variant=source.openingVariants?.[period];
 if(!variant)return source;
 const data=structuredClone(source),delta=variant.board.seconds-data.boards[0].seconds;
 data.boards[0]=structuredClone(variant.board);
 const shift=(x,keys)=>{for(const key of keys)if(Number.isFinite(x[key]))x[key]+=delta;};
 for(const b of data.boards.slice(1)){shift(b,['start','end','eraseStart','writeStart','writeEnd','breakCountdownStart']);for(const cue of b.lineCues||[])shift(cue,['writeStart','writeEnd','audioStart','audioEnd']);}
 data.chapters[0]={...data.chapters[0],duration:variant.board.seconds,src:variant.board.file.split('/').pop(),file:variant.board.file};
 for(const chapter of data.chapters.slice(1))shift(chapter,['start']);
 data.paragraphs=[...structuredClone(variant.paragraphs),...data.paragraphs.filter(p=>p.page!==0).map(p=>{shift(p,['start','end']);return p;})];
 for(const p of data.periods||[]){if(p.start>0)p.start+=delta;p.end+=delta;}
 data.duration+=delta;data.durationWithoutBreak+=delta;
 data.openingSelection={period,greeting:variant.greeting,clock:'system-local'};
 return data;
}
// Thinking, break and final reading timers use real seconds at every speech rate.
export function classroomAudioRate(board,time,rate=1){
 if(board?.id?.endsWith('-break'))return 1;
 if(board?.waits?.some(w=>time>=w.start&&time<w.end))return 1;
 if(board?.boardHoldSeconds>0&&time>=board.seconds-board.boardHoldSeconds)return 1;
 return rate;
}
export function classroomDuration(manifest,rate=1){
 return manifest.boards.reduce((sum,b)=>{
  if(b.id.endsWith('-break'))return sum+b.seconds;
  const fixed=(b.waits||[]).reduce((n,w)=>n+w.end-w.start,0)+(b.boardHoldSeconds||0);
  return sum+(b.seconds-fixed)/rate+fixed;
 },0);
}
