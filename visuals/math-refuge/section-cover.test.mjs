import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {CLASSROOM_PROGRAMS} from './classroom-catalog.js';
import {CourseDirectory} from './course-directory.js';
const read=name=>JSON.parse(fs.readFileSync(new URL(name,import.meta.url),'utf8'));
test('both section covers and actual opening audio use 子皿曰成',()=>{
 const glyphs=new Set(read('./assets/chalk/chinese36/index.json').glyphs.map(g=>g.char));
 for(const p of CLASSROOM_PROGRAMS){
  const cover=read('./assets/chalk/'+p.id+'/pages.json').pages[0];
  const voice=read('./assets/audio/courses/'+p.id+'/narration.json');
  assert.equal(p.speaker,'子皿曰成');assert.equal(p.speakerEn,'Zimin Yuecheng');
  assert.equal(cover.presenter,'主讲：子皿曰成');assert.equal(cover.assistant,'助教：孟晟');
  assert.equal(cover.coverType,'section');assert(cover.text.includes('§2.6 '+p.sectionPart));
  assert(!/第[一二]课时/.test(cover.title));
  const intro=voice.paragraphs.filter(q=>q.page===0);
  assert.equal(intro.length,3);
  assert.equal(intro[0].spokenText,'大家好，我是本课 AI 主讲子皿曰成。');
  assert(intro[1].spokenText.includes('我的助教是孟晟'));
  assert(intro[2].spokenText.includes('本节课我们学习第二点六节'));
  for(const char of cover.presenter+cover.assistant)if(/[\u3400-\u9fff]/.test(char))assert(glyphs.has(char),'Missing '+char);
 }
});
test('directory expands course then chapter then numbered section, with upper/lower as the playable leaves',()=>{
 const d=new CourseDirectory(read('./assets/courses/algebra-i-sections.json').sections);
 assert.equal(d.level,'courses');assert.equal(d.entries()[0].title,'代数学 I');
 assert(d.enter('algebra-i'));assert.equal(d.level,'chapters');assert.equal(d.entries().length,4);
 assert(d.enter('chapter:2'));const leaves=d.entries();
 assert.deepEqual(leaves.filter(e=>e.program).map(e=>e.title),['2.6 上 · 西罗三大定理','2.6 下 · 西罗定理的应用']);
 assert(leaves.every(e=>!e.branch&&!/课时/.test(e.title)));
 d.page=-10;assert.equal(d.visible().page,0);d.page=99;assert.equal(d.visible().page,1);
 d.back();assert.equal(d.level,'chapters');d.back();assert.equal(d.level,'courses');
});
