// Queue natural strokes through explanation time instead of pausing each line.
const schedules=new WeakMap();
export function writingSchedule(board,writing){
 if(!writing?.physicalTiming)return null;
 let cached=schedules.get(writing);if(cached?.board===board)return cached.value;
 let cursor=board.writeStart;const entries=[];
 const cues=board.lineCues?.length?board.lineCues:[{row:null,writeStart:board.writeStart}];
 for(const cue of cues){const segments=cue.row===null?writing.segments:writing.segments.filter(s=>s.mainLine===cue.row);if(!segments.length)throw Error('Narration row has no visible ink: '+cue.row);
  const from=segments[0].start,to=segments.at(-1).end,start=cursor,end=start+(to-from)/writing.unitsPerSecond;
  entries.push({row:cue.row,start,end,from,to});cursor=end;
 }
 const value={entries,end:cursor,total:writing.total};schedules.set(writing,{board,value});return value;
}
export function scheduledWriting(schedule,time){
 let completed=0;for(const entry of schedule.entries){if(time<entry.start)return{progress:completed/schedule.total,writing:false};if(time<entry.end)return{progress:(entry.from+(entry.to-entry.from)*(time-entry.start)/(entry.end-entry.start))/schedule.total,writing:true};completed=entry.to;}
 return{progress:1,writing:false};
}
export function settledBoardFrame(frame,completed){
 return frame.phase==='write'&&completed.has('write:'+frame.page+':end')?{...frame,phase:'hold',progress:1,writing:false}:frame;
}
// Only unfinished whole-board work and erasing hold the transport.
// Seek snapshots never replay previous unfinished work.
export function narrationWork(manifest,time,previous,writing,erase,completed){
 if(previous===null||time<previous||time-previous>.5)return null;
 const b=manifest.boards.findLast(b=>b.start<=previous);if(!b)return null;
 const crossing=at=>previous<=at&&time>=at;
 const eraseKey='erase:'+b.page;
 if(b.page>=6&&erase&&!completed.has(eraseKey)&&crossing(b.writeStart)){
  const elapsed=Math.max(0,b.writeStart-b.eraseStart-1.8);
  if(erase.duration>elapsed)return{key:eraseKey,kind:'erase',page:b.page,at:b.writeStart,elapsed,duration:erase.duration};
 }
 const schedule=writingSchedule(b,writing),deadline=b.end-.25,key='write:'+b.page+':end';
 if(schedule&&!completed.has(key)&&schedule.end>deadline+.02&&crossing(deadline)){
  const start=scheduledWriting(schedule,deadline).progress*writing.total,end=writing.total;
  return{key,kind:'write',page:b.page,at:deadline,elapsed:0,duration:(end-start)/writing.unitsPerSecond,start,end,total:writing.total};
 }
 return null;
}
export function boardWorkFrame(work){const p=Math.max(0,Math.min(1,work.elapsed/work.duration));return{page:work.page,phase:work.kind==='erase'?'erase':'write',progress:work.kind==='erase'?p:(work.start+p*(work.end-work.start))/work.total,writing:work.kind==='write'&&p<1,ended:false,duration:work.duration};}
