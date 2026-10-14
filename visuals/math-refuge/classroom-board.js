import {wrapBoardText} from './chalk-wrap.js';
export function classroomCountdown(seconds,paused=false,language='zh'){
 const n=Math.max(0,Math.ceil(seconds||0)),time=Math.floor(n/60)+':'+String(n%60).padStart(2,'0');
 return(language==='en'?'Remaining ':'剩余 ')+time+(paused?(language==='en'?' · Paused':' · 已暂停'):'');
}
export function drawClassroomActivity(ctx,activity,{paused=false,language='zh'}={}){
 ctx.save();ctx.fillStyle='#eee9d5';ctx.textBaseline='alphabetic';ctx.textAlign='left';
 const font='RefugeChinese, RefugeLatin, KaiTi, serif',title=activity.activityType==='break'?(language==='en'?'Five-minute break':'课间休息'):(language==='en'?'Classroom exercise':'随堂练习');
 ctx.font='56px '+font;ctx.fillText(title,84,100);let size=50,lines;
 do{ctx.font=size+'px '+font;lines=wrapBoardText(activity.task||activity.title,size,1328,(t,s)=>{ctx.font=s+'px '+font;return ctx.measureText(t).width;},false);if(lines.length<=4)break;size-=2;}while(size>26);
 ctx.font=size+'px '+font;for(const [i,line]of lines.entries())ctx.fillText(line,88,210+i*76);
 ctx.font='42px '+font;ctx.fillStyle='#e4cf9c';ctx.fillText(classroomCountdown(activity.remaining,paused,language),88,590);
 ctx.font='28px '+font;ctx.textAlign='right';ctx.fillText(language==='en'?'Pause below · Right arrow for feedback':'下方播放键可暂停 · 右箭头进入讲评',1448,590);ctx.restore();
 return{lines:lines.length+2,title,countdown:classroomCountdown(activity.remaining,paused,language)};
}
