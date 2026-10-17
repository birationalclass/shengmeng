// Semantic rows wait for narration; strokes within a row never wait.
const schedules=new WeakMap();
export function writingSchedule(board,writing){
 if(!writing?.physicalTiming)return null;
 let cached=schedules.get(writing);if(cached?.board===board)return cached.value;
 let cursor=board.writeStart,previousAudioEnd=board.writeStart,previousUnit;const entries=[];
 const cues=board.lineCues?.length?board.lineCues:[{row:null,writeStart:board.writeStart}];
 for(const cue of cues){const segments=cue.row===null?writing.segments:writing.segments.filter(s=>s.mainLine===cue.row);if(!segments.length)throw Error('Narration row has no visible ink: '+cue.row);
  const from=segments[0].start,to=segments.at(-1).end,start=Math.max(cursor,cue.writeStart??0,cue.writeBeforeSpeech?0:cue.audioStart??0,cue.semanticUnit&&cue.semanticUnit===previousUnit?0:previousAudioEnd),end=start+(to-from)/writing.unitsPerSecond;
  entries.push({row:cue.row,start,end,from,to});cursor=end;previousAudioEnd=cue.audioEnd??end;previousUnit=cue.semanticUnit;
 }
 const value={entries,end:cursor,total:writing.total};schedules.set(writing,{board,value});return value;
}
export function scheduledWriting(schedule,time){
 let completed=0;for(const entry of schedule.entries){if(time<entry.start)return{progress:completed/schedule.total,writing:false};if(time<entry.end)return{progress:(entry.from+(entry.to-entry.from)*(time-entry.start)/(entry.end-entry.start))/schedule.total,writing:true};completed=entry.to;}
 return{progress:1,writing:false};
}
export function settledBoardFrame(frame,completed){
 if(frame.phase!=='write')return frame;
 if(completed.has('write:'+frame.page+':end'))return{...frame,phase:'hold',progress:1,writing:false};
 const prefix='unit:'+frame.page+':',floor=Math.max(0,...[...completed].filter(k=>k.startsWith(prefix)).map(k=>Number(k.slice(prefix.length))));
 return floor>frame.progress?{...frame,progress:floor,writing:false,phase:floor>=1?'hold':'write'}:frame;
}
// Only unfinished whole-board work and erasing hold the transport.
// Seek snapshots never replay previous unfinished work.
export function narrationWork(manifest,time,previous,writing,erase,completed,reviewRemaining=0){
 if(previous===null||time<previous||time-previous>.5)return null;
 const b=manifest.boards.findLast(b=>b.start<=previous);if(!b)return null;
 const crossing=at=>previous<=at&&time>=at;
 const eraseKey='erase:'+b.page;
 if(b.page>=6&&erase&&!completed.has(eraseKey)&&crossing(b.writeStart)){
  const elapsed=Math.max(0,b.writeStart-b.eraseStart-1.8);
  if(erase.duration>elapsed)return{key:eraseKey,kind:'erase',page:b.page,at:b.writeStart,elapsed,duration:erase.duration};
 }
 const schedule=writingSchedule(b,writing),deadline=b.end-.25,key='write:'+b.page+':end';
 if(schedule){const units=new Map();for(const cue of b.lineCues||[])if(cue.writeBeforeSpeech){const id=cue.semanticUnit??cue.row,entry=schedule.entries.find(e=>e.row===cue.row),u=units.get(id)||{at:cue.audioStart-.02,end:0};u.end=Math.max(u.end,entry.from+(entry.to-entry.from)*(cue.speechAtWrittenFraction??1));units.set(id,u);}for(const u of units.values()){const unitKey='unit:'+b.page+':'+u.end/writing.total;if(!completed.has(unitKey)&&crossing(u.at)){const start=scheduledWriting(schedule,u.at).progress*writing.total;if(start<u.end-.0001)return{key:unitKey,kind:'write',page:b.page,at:u.at,elapsed:0,duration:(u.end-start)/writing.unitsPerSecond,start,end:u.end,total:writing.total};}}}
 if(schedule&&!completed.has(key)&&!completed.has('unit:'+b.page+':1')&&schedule.end>deadline+.02&&crossing(deadline)){
  const start=scheduledWriting(schedule,deadline).progress*writing.total,end=writing.total;
  return{key,kind:'write',page:b.page,at:deadline,elapsed:0,duration:(end-start)/writing.unitsPerSecond,start,end,total:writing.total};
 }
 if(reviewRemaining>0&&!completed.has('review:'+b.page+':end')&&crossing(b.end-.02))return{key:'review:'+b.page+':end',kind:'review',page:b.page,at:b.end-.02,elapsed:0,duration:reviewRemaining};
 return null;
}
export function boardWorkFrame(work){const p=Math.max(0,Math.min(1,work.elapsed/work.duration));return{page:work.page,phase:work.kind==='review'?'hold':work.kind==='erase'?'erase':'write',progress:work.kind==='review'?1:work.kind==='erase'?p:(work.start+p*(work.end-work.start))/work.total,writing:work.kind==='write'&&p<1,ended:false,duration:work.duration};}
