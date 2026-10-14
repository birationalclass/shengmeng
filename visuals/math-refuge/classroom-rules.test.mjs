import test from 'node:test';import assert from 'node:assert/strict';import fs from 'node:fs';
import {firstLesson,secondLesson} from './sylow-lesson-outline.mjs';import {TEXTBOOK_SHA256} from './classroom-content-rules.mjs';
import {classroomHeading,drawClassroomMetadata} from './classroom-metadata.js';import {drawClassroomActivity} from './classroom-board.js';import {boardTimeLabel,boardTimePosition} from './board-time.js';
const boards=[...firstLesson,...secondLesson],read=p=>JSON.parse(fs.readFileSync(new URL(p,import.meta.url),'utf8'));
const original=i=>boards.find(b=>b.originalIndex===i);
test('the textbook numbering and conventions are preserved; invented examples receive no textbook number',()=>{
 assert.match(original(2).reference.label[0],/定义 2\.6\.1/);assert(original(2).lines.some(l=>l.tex?.includes(String.raw`1\le r`)));assert(!original(2).lines[0].speech.includes('单位子群也属于'));
 assert.equal(boards[3].reference.label[0],'推论 2');assert.equal(original(32).reference.label[0],'例 1');assert.equal(original(31).reference.label[0],'习题 2-6 · 第 18 题');
 for(const i of [26,27,28,29,30])assert.equal(original(i).reference.kind,'extension');for(const b of boards.filter(b=>b.reference.kind==='textbook'))assert.equal(b.reference.sha256,TEXTBOOK_SHA256);
});
test('the three 15-order proof boards keep their target, start with the normality lemma and color only the proved equalities',()=>{
 const pages=read('./assets/chalk/algebra-sylow/pages.json').pages;
 for(const i of [19,20,21]){const p=pages.find(p=>p.originalIndex===i);assert.equal(p.topic[0],'15 阶群结构');assert.match(p.objective[0],/C₁₅/);assert(!classroomHeading(p,'zh',p.title).includes('§'));}
 const normal=pages.find(p=>p.originalIndex===19);assert.match(normal.boardLines[0].text,/引理.*唯一且正规/);assert.equal(normal.emphasis[3].fragment,String.raw`n_5=1`);assert.equal(normal.emphasis[4].fragment,String.raw`n_3=1`);
});
test('every exercise carries its assumptions and goal; the 30-order question remains understandable in isolation',()=>{
 for(const b of boards){assert(b.exercise.given.length>=8);assert(b.exercise.goal.length>=8);assert(b.exercise.prompt);}
 const b=original(26);assert.match(b.exercise.given,/\|G\|=30/);assert.match(b.exercise.goal,/非平凡真正规子群/);
 const texts=[],ctx=new Proxy({save(){},restore(){},translate(){},scale(){},beginPath(){},moveTo(){},lineTo(){},rect(){},stroke(){},measureText:t=>({width:t.length*20}),fillText:t=>texts.push(t)},{get:(t,k)=>k in t?t[k]:()=>{}});
 drawClassroomActivity(ctx,{activityType:'exercise',exercise:b.exercise,remaining:16});assert(texts.some(t=>t.includes('|G|=30')));assert(texts.some(t=>t.includes('非平凡真正规子群')));
});
test('original textbook questions have dedicated numbered boards before their proofs, without recap or proof text in the question',()=>{
 const pages=read('./assets/chalk/algebra-sylow/pages.json').pages,questions=pages.filter(p=>p.statementOnly);assert.equal(questions.length,4);
 const q=questions.find(p=>p.clipPrefix==='q2-6-8');assert.equal(q.title,'习题2-6 第8题');assert.equal(q.boardLines.map(l=>l.text).join(''),'证明：阶为15的群一定是循环群。');assert.equal(q.mainLineCount,2);assert(pages.indexOf(q)<pages.findIndex(p=>p.originalIndex===19));assert.equal(original(18).reference.kind,'extension');
 for(const p of questions){assert(p.mainLineCount<=6);assert.equal(p.reference.kind,'textbook');assert.equal(p.title,p.reference.label[0]);assert(p.exercise.original[0]);}
 const painted=[],ctx=new Proxy({save(){},restore(){},translate(){},scale(){},beginPath(){},moveTo(){},lineTo(){},rect(){},stroke(){},measureText:t=>({width:t.length*20}),fillText:(t,x,y)=>painted.push({t,x,y})},{get:(t,k)=>k in t?t[k]:()=>{}});drawClassroomMetadata(ctx,pages.find(p=>p.originalIndex===19),23,'zh',{total:pages.length});assert(!painted.some(p=>p.t.startsWith('目标：')),'goal must be readable in title/body, never a tiny footer');
});
test('the smart-screen time uses absolute speech/task time and sits below the pause button',()=>{
 assert.equal(boardTimeLabel({time:65,duration:5700}),'01:05 / 1:35:00');assert.equal(boardTimeLabel({time:65,duration:5700,phase:'paused'}),'01:05 / 1:35:00');assert(boardTimePosition(0).y+.16<-.46);
});
