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
 assert.equal(clock.phase,'hold');assert.equal(clock.active,boardSlot(151));
 assert.deepEqual(clock.slots.map(s=>s.page).sort((a,b)=>a-b),[146,147,148,149,150,151]);
 clock.seek(141);assert.deepEqual(clock.slots.filter(s=>s.page>=0).map(s=>s.page).sort((a,b)=>a-b),[140,141]);
 clock.seek(999);assert.equal(clock.page,181);assert(clock.ended);
 for(let i=0;i<1000;i++)clock.update(.1);assert.equal(clock.page,181);
 clock.seek(-5);assert.equal(clock.page,140);assert(!clock.ended);
});
test('KM reading seminar covers original sections, substantial chapters and a worked erratum',async()=>{
 assert.equal(KM_CHAPTERS.length,7);assert.equal(KM_SECTIONS.length,38);assert.equal(kmOutline.length,248);
 assert.equal(new Set(KM_SECTIONS.map(s=>s.id)).size,38);
 for(const chapter of KM_CHAPTERS){
  assert.equal(kmOutline[chapter.start].kind,'cover');assert.equal(kmOutline[chapter.end].kind,'closing');
  assert(kmOutline.slice(chapter.start,chapter.end).filter(p=>!p.kind).length>=24);
 }
 for(const part of KM_SECTIONS){assert(part.goal&&part.prerequisites);assert.equal(part.end-part.start+1,part.boards);assert(kmOutline.slice(part.start,part.end+1).every(p=>p.section===part.id));}
 const pages=JSON.parse(await fs.readFile(new URL('./assets/chalk/km/pages.json',import.meta.url),'utf8')).pages;
 assert.equal(pages.length,248);
 const errata=pages.filter(p=>p.title.startsWith('勘误'));assert.equal(errata.length,7); // includes the preliminary convention reminder.
 assert(pages.some(p=>p.tex.includes('=-1\\ne0=')));
 assert(pages.some(p=>p.text.includes('不能把整条引理统称为错误')));
 assert.equal(pages.filter(p=>p.diagram).length,4);
 for(const p of pages){assert(p.en.title&&p.en.source);await fs.access(new URL(p.formulaAsset,import.meta.url));const svg=await fs.readFile(new URL(p.formulaAsset,import.meta.url),'utf8');assert(!svg.includes('data-mjx-error'));}
});
