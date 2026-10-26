export function isClassroomBreak(page){return page?.period==='break'||page?.kind==='break';}
export function classroomBreakTime(page,board,voice={}){
 if(!isClassroomBreak(page))return null;
 const activity=voice.activity,remaining=Number.isFinite(activity?.remaining)&&activity?.activityType==='break'?activity.remaining:(board?.end??voice.time??0)-(voice.time??0);
 const seconds=Math.max(0,Math.min(300,Math.ceil(remaining-1e-6)));
 return{seconds,text:String(Math.floor(seconds/60)).padStart(2,'0')+':'+String(seconds%60).padStart(2,'0')};
}
