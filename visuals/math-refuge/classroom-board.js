import {wrapBoardText} from './chalk-wrap.js';
import {drawReferenceIcon} from './classroom-metadata.js?v=textbook-problems-1';
export function classroomCountdown(seconds,paused=false,language='zh'){
 const n=Math.max(0,Math.ceil(seconds||0)),time=Math.floor(n/60)+':'+String(n%60).padStart(2,'0');
 return(language==='en'?'Remaining ':'剩余 ')+time+(paused?(language==='en'?' · Paused':' · 已暂停'):'');
}
// Preserve goal metadata, but show the canonical prompt only once.
export function classroomExerciseSheets(activity,language='zh',measure){
 const e=activity.exercise,en=language==='en',pick=v=>Array.isArray(v)?v[en?1:0]:v;
 const normalize=s=>String(s||'').replace(/[\s，。,:：;；、.?!？！]/g,'');
 let prompt=e?(en&&e.promptEn?e.promptEn:pick(e.prompt||e.goal)):'';
 const goal=e?(en&&e.goalEn?e.goalEn:pick(e.goal)):'';
 if(goal&&!normalize(prompt).includes(normalize(goal)))prompt=goal.replace(/[。.]$/,'')+'。'+prompt;
 const blocks=e?.original?[pick(e.original)]:e?[...(e.given?[en&&e.givenEn?'Given: '+e.givenEn:'已知：'+pick(e.given)]:[]),(en&&e.promptEn?'Question: ':'问题：')+prompt]:[activity.task||activity.title||''];
 const wrap=text=>wrapBoardText(text,38,1328,measure,false);
 const question=blocks.flatMap(wrap).map(text=>({text,role:'question'})),sheets=[];
 for(let i=0;i<question.length;i+=5)sheets.push(question.slice(i,i+5));
 if(!sheets.length)sheets.push([]);
 if(activity.feedback&&activity.answer){
  const answer=wrap((en&&activity.answerEn?'Solution: ':'解：')+(en&&activity.answerEn?activity.answerEn:activity.answer)).map(text=>({text,role:'answer'}));
  for(const line of answer){if(sheets.at(-1).length===5)sheets.push([]);sheets.at(-1).push(line);}
 }
 return sheets;
}
// The same exercise surface remains visible throughout its feedback chapter.
export function classroomActivityAt(manifest,time,page){
 const task=manifest?.chapters.find(c=>c.kind==='activity'&&c.activityType==='exercise'&&c.page===page);
 if(!task)return null;
 const intro=manifest.paragraphs?.find(p=>p.page===page&&p.role==='task'),feedback=manifest.chapters.find(c=>c.page===page&&c.feedback);
 if(time<(intro?.start??task.start)||time>=(feedback?feedback.start+feedback.duration:task.start+task.duration))return null;
 const answering=Boolean(feedback&&time>=feedback.start),answer=manifest.paragraphs?.find(p=>p.page===page&&p.role==='answer')?.text?.replace(/^我们核对一下[。．.!！]?/,'')||'';
 return {...task,remaining:Math.max(0,task.start+task.duration-time),feedback:answering,answer:answering?answer:'',feedbackProgress:answering?Math.min(1,(time-feedback.start)/feedback.duration):0};
}
export function drawClassroomActivity(ctx,activity,{paused=false,language='zh',sheetIndex}={}){
 ctx.save();ctx.fillStyle='#eee9d5';ctx.textBaseline='alphabetic';ctx.textAlign='left';
 const font='RefugeChinese, RefugeLatin, KaiTi, serif',exercise=activity.exercise,book=exercise?.reference?.kind==='textbook',title=activity.activityType==='break'?(language==='en'?'Five-minute break':'课间休息'):book?exercise.reference.label[language==='en'?1:0]:(language==='en'?'Classroom exercise':'随堂练习');
 ctx.fillStyle='#e4cf9c';ctx.font='52px '+font;drawReferenceIcon(ctx,book?'textbook':'extension',84,60,36);ctx.fillText(title,136,100);
 const sheets=classroomExerciseSheets(activity,language,(t,size)=>{ctx.font=size+'px '+font;return ctx.measureText(t).width;});
 const at=Math.max(0,Math.min(sheets.length-1,sheetIndex??(activity.feedback?Math.floor(activity.feedbackProgress*sheets.length):0)));
 ctx.font='38px '+font;ctx.fillStyle='#eee9d5';for(const [i,line]of sheets[at].entries())ctx.fillText(line.text,88,175+i*72);
 ctx.font='32px '+font;ctx.fillStyle='#e4cf9c';ctx.fillText(activity.feedback?(language==='en'?'Solution':'讲评'):classroomCountdown(activity.remaining,paused,language),88,590);
 ctx.font='22px "Microsoft YaHei", "Segoe UI", sans-serif';ctx.textAlign='right';
 ctx.fillText(sheets.length>1?(language==='en'?`Exercise board ${at+1} / ${sheets.length}`:`练习第 ${at+1} / ${sheets.length} 板`):language==='en'?'Pause below · Right arrow to continue':'下方播放键可暂停 · 右箭头继续',1448,590);ctx.restore();
 const eraseRows=[[84,48,Math.min(1368,measureTextWidth(ctx,title,font,52)+64),60],...sheets[at].map((line,i)=>[84,139+i*72,Math.min(1336,measureTextWidth(ctx,line.text,font)+8),48])];
 return{lines:sheets[at].length+1,title,feedback:Boolean(activity.feedback),sheetIndex:at,sheetCount:sheets.length,eraseRows,countdown:classroomCountdown(activity.remaining,paused,language)};
}
function measureTextWidth(ctx,text,font,size=38){ctx.save();ctx.font=size+'px '+font;const width=ctx.measureText(text).width;ctx.restore();return width;}
