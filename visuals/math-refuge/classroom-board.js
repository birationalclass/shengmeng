import {wrapBoardText} from './chalk-wrap.js';
import {drawReferenceIcon} from './classroom-metadata.js?v=textbook-problems-1';
export function classroomCountdown(seconds,paused=false,language='zh'){
 const n=Math.max(0,Math.ceil(seconds||0)),time=Math.floor(n/60)+':'+String(n%60).padStart(2,'0');
 return(language==='en'?'Remaining ':'剩余 ')+time+(paused?(language==='en'?' · Paused':' · 已暂停'):'');
}
export function drawClassroomActivity(ctx,activity,{paused=false,language='zh'}={}){
 ctx.save();ctx.fillStyle='#eee9d5';ctx.textBaseline='alphabetic';ctx.textAlign='left';
 const font='RefugeChinese, RefugeLatin, KaiTi, serif',exercise=activity.exercise,book=exercise?.reference?.kind==='textbook',title=activity.activityType==='break'?(language==='en'?'Five-minute break':'课间休息'):book?exercise.reference.label[language==='en'?1:0]:(language==='en'?'Classroom exercise':'随堂练习');
 ctx.font='52px '+font;drawReferenceIcon(ctx,book?'textbook':'extension',84,60,36);ctx.fillText(title,136,100);let size=38,lines;
 const blocks=exercise?.original?[['',exercise.original[language==='en'?1:0]]]:exercise?[['已知：',exercise.given],['目标：',exercise.goal],['问题：',exercise.prompt]]:[['',activity.task||activity.title]];
 do{lines=blocks.flatMap(([label,text])=>wrapBoardText(label+text,size,1328,(t,s)=>{ctx.font=s+'px '+font;return ctx.measureText(t).width;},false));if(lines.length<=5)break;size-=2;}while(size>26);
 if(lines.length>5)throw Error('Exercise needs another board: '+title);ctx.font=size+'px '+font;for(const [i,line]of lines.entries())ctx.fillText(line,88,165+i*Math.min(66,350/Math.max(1,lines.length)));
 ctx.font='42px '+font;ctx.fillStyle='#e4cf9c';ctx.fillText(classroomCountdown(activity.remaining,paused,language),88,590);
 ctx.font='28px '+font;ctx.textAlign='right';ctx.fillText(language==='en'?(activity.activityType==='break'?'Pause below · Right arrow to continue':'Pause below · Right arrow for feedback'):(activity.activityType==='break'?'下方播放键可暂停 · 右箭头提前继续':'下方播放键可暂停 · 右箭头进入讲评'),1448,590);ctx.restore();
 return{lines:lines.length+1,title,countdown:classroomCountdown(activity.remaining,paused,language)};
}
