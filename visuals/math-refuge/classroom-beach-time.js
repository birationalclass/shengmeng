export const CLASSROOM_BREAK_SECONDS=300;
export const CLASSROOM_BREAK_CLOUD=.5;
export function classroomBreakHour(date=new Date()){
 const parts=new Intl.DateTimeFormat('en-GB',{timeZone:'Asia/Shanghai',hour:'2-digit',minute:'2-digit',second:'2-digit',hourCycle:'h23'}).formatToParts(date);
 const value=type=>Number(parts.find(p=>p.type===type).value);
 return value('hour')+value('minute')/60+value('second')/3600;
}
// Derive the whole day from the same monotonic clock as the countdown. Neither
// frame rate nor the normal scene's 60x preview limit can shorten the day.
export function classroomBreakTime(startHour,elapsed,duration=CLASSROOM_BREAK_SECONDS){
 const fraction=Math.max(0,Math.min(1,elapsed/duration)),hours=fraction*24,total=startHour+hours;
 return {startHour,dayHours:hours,sceneHour:((total%24)+24)%24,dayOffset:Math.floor(total/24),timeRate:86400/duration,cloudCoverage:CLASSROOM_BREAK_CLOUD};
}
