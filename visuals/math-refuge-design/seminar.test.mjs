import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {LectureClock,boardSlot} from './lecture-state.js';
import {teachingRoomAt} from './room-context.js';
import {SEMINAR,seminarFloor} from './seminar-layout.js';
import {BUILDING_SCALE as S,DECK_Y} from './site-layout.js';
import {KM_CHAPTERS,KM_SECTIONS,kmOutline} from './km-seminar-outline.mjs';
test('teaching controls belong to physical rooms including upper storeys, not outdoor paths',()=>{
 assert.equal(teachingRoomAt({x:40*S,y:DECK_Y*S+1.5,z:0}),0);
 assert.equal(teachingRoomAt({x:40*S,y:DECK_Y*S+5.5,z:0}),-1);
 for(let i=0;i<3;i++){
  assert.equal(teachingRoomAt({x:-84*S,y:seminarFloor(i)*S+1.5,z:8*S}),i+1);
  assert.equal(teachingRoomAt({x:-89*S,y:seminarFloor(i)*S+1.5,z:8*S}),-1,'Exterior landing is not a classroom');
  assert.equal(teachingRoomAt({x:-84*S,y:seminarFloor(i)*S+SEMINAR.clearHeight+.05,z:8*S}),-1);
 }
 assert.equal(teachingRoomAt({x:0,y:2,z:0}),-1);
});
test('manual seeking reconstructs history and ends chapter playback without lift or erase',()=>{
 const clock=new LectureClock(248);clock.startAt=140;clock.stopAt=181;clock.seek(151);
 assert.equal(clock.phase,'hold');assert.equal(clock.active,boardSlot(151-140));
 assert.deepEqual(clock.slots.map(s=>s.page).sort((a,b)=>a-b),[146,147,148,149,150,151]);
 clock.seek(141);assert.deepEqual(clock.slots.filter(s=>s.page>=0).map(s=>s.page).sort((a,b)=>a-b),[140,141]);
 clock.seek(999);assert.equal(clock.page,181);assert(clock.ended);
 for(let i=0;i<1000;i++)clock.update(.1);assert.equal(clock.page,181);
 clock.seek(-5);assert.equal(clock.page,140);assert(!clock.ended);
});
test('KM reading seminar covers original sections, substantial chapters and a worked erratum',async()=>{
 assert.equal(KM_CHAPTERS.length,7);assert.equal(KM_SECTIONS.length,38);assert(kmOutline.length>200);
 assert.equal(new Set(KM_SECTIONS.map(s=>s.id)).size,38);
 for(const chapter of KM_CHAPTERS){
  assert.equal(kmOutline[chapter.start].kind,'cover');assert.equal(kmOutline[chapter.end].kind,'closing');
  assert(kmOutline.slice(chapter.start,chapter.end).filter(p=>!p.kind).length>=24);
 }
 for(const part of KM_SECTIONS){assert(part.goal&&part.prerequisites);assert.equal(part.end-part.start+1,part.boards+2);assert.equal(kmOutline[part.start].kind,'cover');assert.equal(kmOutline[part.end].kind,'closing');assert(kmOutline.slice(part.start,part.end+1).every(p=>p.section===part.id));}
 const pages=JSON.parse(await fs.readFile(new URL('./assets/chalk/km/pages.json',import.meta.url),'utf8')).pages;
 assert.equal(pages.length,kmOutline.length);
 const errata=pages.filter(p=>p.title.startsWith('勘误'));assert.equal(errata.length,7); // includes the preliminary convention reminder.
 assert(pages.some(p=>p.tex.includes('=-1\\ne0=')));
 assert(pages.some(p=>p.text.includes('不能把整条引理统称为错误')));
 assert.equal(pages.filter(p=>p.diagram).length,4);
 for(const p of pages){assert(p.en.title&&p.en.source);await fs.access(new URL(p.formulaAsset,import.meta.url));const svg=await fs.readFile(new URL(p.formulaAsset,import.meta.url),'utf8');assert(!svg.includes('data-mjx-error'));}
});

import {classroomVisible} from './classroom-visibility.js';
test('offscreen clock advances without rendering, keeps partial ink and stops at the selected section',()=>{
 const clock=new LectureClock(100);clock.startAt=20;clock.stopAt=28;clock.seek(20);
 for(let i=20;i<=28;i++)clock.setDurations(i,{write:10,erase:3,hold:2,lift:1});
 clock.advance(2+1+5);assert.equal(clock.page,21);assert.equal(clock.phase,'write');assert.equal(clock.slots[clock.active].progress,.5);
 clock.advance(10000);assert.equal(clock.page,28);assert(clock.ended);assert.equal(clock.slots[clock.active].progress,1);
 clock.advance(10000);assert.equal(clock.page,28);assert(!clock.slots.some(s=>s.page<20&&s.page>=0));
});
test('classroom visibility gates distant, behind-camera and other-floor boards with hysteresis',()=>{
 const state={distance:10,inFrustum:true,eyeY:2,floorY:0,height:3.8,insideRoom:1,room:1};
 assert(classroomVisible(state));assert(!classroomVisible({...state,inFrustum:false}));
 assert(!classroomVisible({...state,insideRoom:2}));assert(!classroomVisible({...state,distance:25}));
 assert(classroomVisible({...state,distance:25,wasVisible:true}));assert(!classroomVisible({...state,distance:29,wasVisible:true}));
 assert(!classroomVisible({...state,insideRoom:-1,eyeY:8}));
});

import {composeChalkPage} from './chalk-language.js';
test('seminar bodies write mathematics first without repeated headings; opening and closing boards stay',async()=>{
 const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/km/pages.json',import.meta.url),'utf8'));
 const calls=[],ctx={clearRect(){},fillText(text,x,y){calls.push({text,y});},drawImage(){},measureText(t){return {width:[...t].length*20};}};
 for(const language of ['zh','en']){
  for(const page of pages.filter(p=>!p.kind)){
   calls.length=0;const rows=composeChalkPage(ctx,page,0,language,{});
   assert(page.hideHeading);assert(!calls.some(c=>c.y===76));assert.equal(rows.find(r=>r.formulaRow!==undefined).formulaRow,0,'Formula sequence begins with the first equation');
   const svg=await fs.readFile(new URL(page.asset,import.meta.url),'utf8');assert(!svg.includes('<text x="84" y="76"'));
  }
  for(const kind of ['cover','closing']){
   calls.length=0;composeChalkPage(ctx,pages.find(p=>p.kind===kind),0,language,{}, {hideHeading:true});assert(calls.length>0,kind+' must still display its title');
  }
  const page={...pages[1],hideHeading:false};calls.length=0;composeChalkPage(ctx,page,0,language,{});assert(calls.some(c=>c.y===76),'Main auditorium keeps its report headings');
  calls.length=0;composeChalkPage(ctx,page,0,language,{}, {hideHeading:true});assert(!calls.some(c=>c.y===76),'Other seminar rooms can opt out independently');
 }
});
