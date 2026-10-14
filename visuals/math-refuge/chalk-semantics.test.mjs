import test from 'node:test';import assert from 'node:assert/strict';import fs from 'node:fs';
import {firstLesson,secondLesson} from './sylow-lesson-outline.mjs';
import {drawClassroomMetadata,REFERENCE_ICON_PATHS} from './classroom-metadata.js';
test('semantic targets exist exactly in the intended line, and order-21 count results are blue',()=>{
 const boards=[...firstLesson,...secondLesson];for(const b of boards)for(const [row,mark]of Object.entries(b.emphasis||{})){const line=b.lines[Number(row)-1];assert(line,b.title);if(mark.fragment)assert(line.tex.includes(mark.fragment),b.title+': '+mark.fragment);}
 const p=boards.find(b=>b.originalIndex===22);assert.deepEqual(p.emphasis[3],{fragment:String.raw`n_7=1`,tone:'conclusion'});assert.deepEqual(p.emphasis[5],{fragment:String.raw`n_3\in\{1,7\}`,tone:'conclusion'});
 const regular=boards.find(b=>b.originalIndex===10);assert.equal(regular.emphasis[4].tone,'conclusion');assert.equal(regular.emphasis[5].tone,'caution');
});
test('automatic metadata has no chalk icon or extension label and retains section/folio while erasing',()=>{
 const texts=[],ctx={save(){},restore(){},fillText(t,x,y){texts.push({t,x,y});}};
 drawClassroomMetadata(ctx,{classroom:true,statementOnly:true,reference:{kind:'textbook'},source:'§2.6'},20,'zh',{total:44});
 assert(texts.some(p=>p.t==='§2.6'));assert(texts.some(p=>p.t==='第 21 / 44 页'));assert(texts.every(p=>p.y===28||p.y===625));
 texts.length=0;drawClassroomMetadata(ctx,{classroom:true,reference:{kind:'extension',label:['扩展','Extension']}},27,'zh',{total:44});assert(!texts.some(p=>p.t.includes('扩展')));
});
test('book and puzzle are the original course-homepage paths',()=>{
 const source=fs.readFileSync(new URL('../../courses/abstract-algebra/2026-fall/lesson-1/screen.js',import.meta.url),'utf8');
 for(const paths of Object.values(REFERENCE_ICON_PATHS))for(const path of paths)assert(source.includes('d="'+path+'"'));
});
