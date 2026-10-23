import {createClassroomBeachBreak} from './classroom-beach-break.js';

// The 3D classroom keeps its own renderer and existing campus. Only its camera
// visits a coastal route; the lesson output stays paused until the return is ready.
export function createMainClassroomBeachBreak({getLecture,getStartHour,enterCoast,moveCoast,returnToClassroom,onCancel,onError}={}){
 let owner=null,identity='',page=-1,returning=false;
 const current=()=>owner&&getLecture()===owner&&owner.report.id===identity&&owner.clock.page===page;
 const beach=createClassroomBeachBreak({inPlace:true,
  onStart:s=>enterCoast(s),
  onProgress:s=>moveCoast(s),
  onError,
  async onFinish(s){
   if(!current())return;returning=true;const target=owner,id=identity,next=page+1;
   try{
    if(next>=target.pages.length)return;
    const destination=target.voiceManifest?.boards.find(b=>b.page===next);
    const ok=destination?await target.voiceSeek(destination.start):await target.seek(next,{preservePlayback:false});
    if(ok===false||getLecture()!==target||target.report.id!==id)return;
    await returnToClassroom(target);
    if(beach.state?.key===s.key&&getLecture()===target&&target.report.id===id&&s.resume)target.playing=true;
   }catch(error){onError?.(error.message);}finally{returning=false;owner=null;}
  },
  onCancel(){owner=null;onCancel?.();}
 });
 function update(){
  if(beach.state){if(!returning&&!current())beach.cancel();return;}
  if(returning)return;const target=getLecture(),index=target?.clock.page,board=target?.pages[index];
  if(!target||target.report.kind!=='classroom'||!target.playing||!(board?.period==='break'||board?.orderedBoard?.kind==='break'))return;
  owner=target;identity=target.report.id;page=index;const item=target.voiceManifest?.boards.find(b=>b.page===index),elapsed=Math.max(0,target.voiceState.time-(item?item.end-300:target.voiceState.time));
  target.playing=false;
  void beach.start({key:identity+':'+page,duration:300,elapsed:Math.min(300,elapsed),playing:true,startHour:getStartHour?.()});
 }
 return {update,cancel:()=>beach.cancel(),toggle(){if(beach.state?.playing)beach.pause();else beach.play();},get state(){return beach.state;}};
}
