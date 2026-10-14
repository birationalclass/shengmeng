// Extend only physical work that does not fit its spoken cue. Audio pauses at
// the cue boundary; seek snapshots never run through earlier unfinished work.
export function narrationWork(manifest,time,previous,writing,erase,completed){
 if(previous===null||time<previous||time-previous>.5)return null;
 const b=manifest.boards.findLast(b=>b.start<=previous);if(!b)return null;
 const crossing=at=>previous<=at&&time>=at;
 const eraseKey='erase:'+b.page;
 if(b.page>=6&&erase&&!completed.has(eraseKey)&&crossing(b.writeStart)){
  const elapsed=Math.max(0,b.writeStart-b.eraseStart-1.8);
  if(erase.duration>elapsed)return{key:eraseKey,kind:'erase',page:b.page,at:b.writeStart,elapsed,duration:erase.duration};
 }
 if(!writing?.physicalTiming)return null;
 const cues=b.lineCues?.length?b.lineCues:[{row:null,writeStart:b.writeStart,writeEnd:b.writeEnd}];
 for(const c of cues){const key='write:'+b.page+':'+c.row;if(completed.has(key)||!crossing(c.writeEnd))continue;
  const segments=c.row===null?writing.segments:writing.segments.filter(s=>s.mainLine===c.row);if(!segments.length)continue;
  const start=segments[0].start,end=segments.at(-1).end,duration=(end-start)/writing.unitsPerSecond,elapsed=c.writeEnd-c.writeStart;
  if(duration>elapsed+.02)return{key,kind:'write',page:b.page,at:c.writeEnd,elapsed,duration,start,end,total:writing.total};
 }
 return null;
}
export function boardWorkFrame(work){const p=Math.max(0,Math.min(1,work.elapsed/work.duration));return{page:work.page,phase:work.kind==='erase'?'erase':'write',progress:work.kind==='erase'?p:(work.start+p*(work.end-work.start))/work.total,writing:work.kind==='write'&&p<1,ended:false,duration:work.duration};}
