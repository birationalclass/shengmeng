import test from 'node:test';import assert from 'node:assert/strict';
import {writingPlan,writingPose,erasingPlan,ERASER_SPEED} from './chalk-motion.js';
import {narrationWork,boardWorkFrame} from './board-work.js';
import {rowNarrationProgress,narrationFrame,syncNarrationClock} from './report-voice.js';
import {LectureClock,boardSlot} from './lecture-state.js';
const stroke=(points,meta)=>Object.assign([0,0,200,40],{strokePath:points,mainLine:0,...meta});
test('Chinese lift has continuous board contact and a visible eased transfer without changing its stroke budget',()=>{
 const rows=[stroke([[0,0],[30,0]],{strokeSeconds:1/16,strokeRaster:{group:'一'}}),stroke([[300,0],[330,0]],{strokeSeconds:1/16,strokeRaster:{group:'二'}})],p=writingPlan(rows),move=p.segments.find(s=>s.row===1&&s.entering);
 assert(move.cost/p.unitsPerSecond>=.065);assert.equal(writingPose(rows,move.start/p.total).toolLift,0);assert(writingPose(rows,(move.start+move.cost/2)/p.total).toolLift<=.018);assert(Math.abs(writingPose(rows,move.end/p.total).toolLift)<1e-12);
 const contact=p.segments.filter(s=>s.contact).reduce((n,s)=>n+s.cost,0)/p.unitsPerSecond;assert(Math.abs(contact-2/16)<1e-9);
 const a=writingPose(rows,(move.start+move.cost*.01)/p.total),b=writingPose(rows,(move.start+move.cost*.99)/p.total);assert(a.x-30<1);assert(b.x>299);
});
test('small English letter strokes share a readable character budget at every font size',()=>{
 for(const scale of [1,5]){const letterGroup={};const p=writingPlan([stroke([[0,0],[2*scale,0]],{letterGroup,letterSeconds:.125}),stroke([[2*scale,0],[3*scale,scale]],{letterGroup,letterSeconds:.125})]);assert(p.letterTiming);assert(Math.abs(p.segments.filter(s=>s.contact).reduce((n,s)=>n+s.cost,0)/p.unitsPerSecond-.25)<1e-9);}
});
test('short narration windows borrow explanation time without a row pause or an instant reveal',()=>{
 const p=writingPlan([stroke([[0,0],[10,0]],{letterSeconds:2})]),m={duration:20,boards:[{page:0,start:0,eraseStart:0,writeStart:0,writeEnd:10,end:20,lineCues:[{row:0,writeStart:2,writeEnd:2.5}]}]};
 assert(rowNarrationProgress(m.boards[0].lineCues,2.25,p)<.2);assert.equal(narrationWork(m,2.51,2.49,p,null,new Set()),null);const f=narrationFrame(m,2.51,p);assert(f.progress<.3);assert(f.writing);assert.equal(narrationFrame(m,5,p).progress,1);
});

test('a compressed narrated erase uses its measured sweep speed, retains the old board and completes before new ink',()=>{
 const erase=erasingPlan(null,[[0,0,1000,200]]);assert(erase.duration>=6);assert(erase.duration<30);
 const m={duration:160,boards:[{page:6,start:120,eraseStart:122,writeStart:125,writeEnd:140,end:160}]},clock=new LectureClock(8);
 const w=narrationWork(m,125.01,124.99,null,erase,new Set());assert.equal(w.kind,'erase');assert.equal(w.elapsed,1.2);const f=boardWorkFrame(w);syncNarrationClock(clock,f,boardSlot);assert.equal(clock.slots[boardSlot(6)].page,0);assert(clock.slots.every(s=>s.page<6));assert(narrationFrame(m,124,null,erase).progress<.1);
 const before=narrationFrame(m,124,null,erase);syncNarrationClock(clock,before,boardSlot);assert.equal(clock.duration,erase.duration,'a short narration gap must never overwrite the measured erase duration');
});


test('formula paths and sampled ink gaps also lift continuously without depth jumps',()=>{
 const pathRows=[stroke([[0,0],[10,0]],{}),stroke([[20,0],[30,0]],{})];
 const guides=[[10,10,null,null,10,10]];guides[0].inkColumns=[0,1,4,5];
 for(const [rows,g] of [[pathRows,undefined],[[[0,0,25,20]],guides]]){
  const p=writingPlan(rows,g);
  for(const segment of p.segments){
   assert(Number.isFinite(segment.liftHeight));
   assert(Math.abs(writingPose(rows,segment.start/p.total,g).toolLift)<1e-10);
   assert(Math.abs(writingPose(rows,segment.end/p.total,g).toolLift)<1e-10);
   if(!segment.contact&&segment.a.some((v,i)=>v!==segment.b[i]))assert(segment.cost/p.unitsPerSecond>=.035-1e-9);
  }
 }
});
