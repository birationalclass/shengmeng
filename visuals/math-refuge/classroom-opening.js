import {MIN_BOARD_REVIEW_SECONDS,boardReviewStart} from './board-review.js?v=course-packs-20261026';
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
 const emphasis=board?.deliveryRanges?.find(r=>time>=r.start&&time<r.end);
 const speechRate=Number.isFinite(board?.playbackRate)?rate*board.playbackRate/(board.rateBaseline||1):rate;
 if(emphasis)return speechRate*emphasis.rateMultiplier;
 return speechRate;
}
export function classroomDuration(manifest,rate=1){
 return manifest.boards.reduce((sum,b)=>{
  if(b.id.endsWith('-break'))return sum+b.seconds;
  const reviewStart=boardReviewStart(b),boundaries=new Set([0,b.seconds,Math.min(b.seconds,reviewStart)]);
  if(Number.isFinite(b.lastStrokeEnd))boundaries.add(b.lastStrokeEnd);
  for(const r of [...(b.waits||[]),...(b.deliveryRanges||[])]){boundaries.add(r.start);boundaries.add(r.end);}
  if(b.boardHoldSeconds>0)boundaries.add(b.seconds-b.boardHoldSeconds);
  const points=[...boundaries].sort((a,b)=>a-b);let total=0,reading=0;
  for(let i=1;i<points.length;i++){const start=points[i-1],end=points[i],seconds=(end-start)/classroomAudioRate(b,(start+end)/2,rate);total+=seconds;if(start>=reviewStart)reading+=seconds;}
  return sum+total+(Math.max(0,MIN_BOARD_REVIEW_SECONDS-reading));
 },0);
}
