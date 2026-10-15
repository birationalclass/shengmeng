import test from 'node:test';import assert from 'node:assert/strict';import fs from 'node:fs';
import {drawClassroomActivity,classroomCountdown,classroomExerciseSheets,classroomActivityAt} from './classroom-board.js';
import {reportControlLayout,bindVoiceFocusPause} from './report-voice.js';
test('all tray controls share one non-overlapping physical strip',()=>{
 for(const column of [0,1,2]){const p=reportControlLayout(column),buttons=['language','previous','voice','next','time','camera','zoomOut','zoomIn','reveal'].map(k=>p[k]);for(let i=1;i<buttons.length;i++)assert(buttons[i-1].x+buttons[i-1].width/2<buttons[i].x-buttons[i].width/2);assert(buttons[0].x-buttons[0].width/2>p.center-2.6);assert(buttons.at(-1).x+buttons.at(-1).width/2<p.center+2.6);}
});
test('exercise goals are not duplicated, feedback retains the question, and overflow adds sheets at the same legible size',()=>{
 const exercise={given:'已知有限群',goal:'说明归纳参数',prompt:'说明归纳参数'};
 const measure=(t,size)=>[...t].length*size;
 const question=classroomExerciseSheets({exercise},'zh',measure).flat().map(l=>l.text).join('');
 assert.equal((question.match(/说明归纳参数/g)||[]).length,1);assert(!question.includes('目标：'));
 const sheets=classroomExerciseSheets({exercise,feedback:true,answer:'用归纳法。'.repeat(100)},'zh',measure);
 assert(sheets.length>1);assert(sheets.every(s=>s.length<=5));assert(sheets[0].some(l=>l.text.includes('有限群')));
 const manifest={chapters:[{kind:'activity',activityType:'exercise',page:2,start:10,duration:20,exercise},{page:2,start:30,duration:10,feedback:true}],paragraphs:[{page:2,role:'task',start:8},{page:2,role:'answer',text:'我们核对一下。归纳阶数。'}]};
 assert.equal(classroomActivityAt(manifest,7,2),null);assert.equal(classroomActivityAt(manifest,15,2).answer,'');
 const feedback=classroomActivityAt(manifest,31,2);assert.equal(feedback.feedback,true);assert.equal(feedback.answer,'归纳阶数。');assert.equal(feedback.exercise,exercise);
 assert.equal(classroomActivityAt(manifest,40,2),null);
});
test('loss of window focus pauses explicitly and focus never starts playback',()=>{
 const doc=new EventTarget(),win=new EventTarget();doc.hidden=false;let pauses=0;const release=bindVoiceFocusPause({pause(){pauses++;}},{documentTarget:doc,windowTarget:win});win.dispatchEvent(new Event('blur'));assert.equal(pauses,1);win.dispatchEvent(new Event('focus'));assert.equal(pauses,1);doc.dispatchEvent(new Event('visibilitychange'));assert.equal(pauses,1);doc.hidden=true;doc.dispatchEvent(new Event('visibilitychange'));assert.equal(pauses,2);release();win.dispatchEvent(new Event('blur'));assert.equal(pauses,2);
});
test('all authored tasks and the countdown stay within six blackboard lines',()=>{
 const plan=JSON.parse(fs.readFileSync(new URL('./assets/chalk/algebra-sylow/lesson-plan.json',import.meta.url)));const painted=[];const ctx={font:'',save(){},restore(){},fillText(text,x,y){painted.push({text,x,y});},measureText(t){const size=Number(this.font.match(/\d+/)[0]);return{width:[...t].reduce((n,c)=>n+(/[\u3400-\u9fff]/.test(c)?1:.55)*size,0)};}};
 for(const b of plan.boards.filter(b=>b.kind==='body')){painted.length=0;const frame=drawClassroomActivity(ctx,{task:b.activity,title:b.title,remaining:41,activityType:'exercise'});assert(frame.lines<=6,b.title);assert(painted.every(p=>p.y>0&&p.y<640));assert(painted.some(p=>p.text==='剩余 0:41'));}
 assert.equal(classroomCountdown(0,true),'剩余 0:00 · 已暂停');assert.equal(classroomCountdown(299.8,false),'剩余 5:00');
});
