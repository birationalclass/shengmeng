import test from 'node:test';import assert from 'node:assert/strict';
import {chineseMetrics,CHINESE_STROKE_SECONDS} from './chinese-chalk.js';
import {writingPlan,rasterStrokeReveal} from './chalk-motion.js';
import {rowNarrationProgress,narrationFrame} from './report-voice.js';
const row=(scale=1,line=0)=>Object.assign([10,20,200*scale,40*scale],{strokePath:[[10,20],[10+20*scale,20],[10+200*scale,20+40*scale]],strokeRaster:{},strokeSeconds:CHINESE_STROKE_SECONDS,mainLine:line});
test('each Chinese stroke retains its time budget when glyph size or path length changes',()=>{
 const a=writingPlan([row()]),b=writingPlan([row(4)]);const contact=p=>p.segments.filter(s=>s.contact).reduce((n,s)=>n+s.cost,0)/p.unitsPerSecond;
 assert(Math.abs(contact(a)-1/16)<1e-9);assert(Math.abs(contact(b)-contact(a))<1e-9);assert.equal(a.chineseStrokeTiming,true);
 const many=writingPlan(Array.from({length:13},()=>row()));assert(Math.abs(contact(many)-13/16)<1e-8);
});
test('a later Chinese stroke remains hidden until its own contact interval',()=>{const rows=[row(1,0),row(1,1)];const p=writingPlan(rows);const firstContact=p.segments.find(s=>s.contact);const progress=(firstContact.start+firstContact.cost/2)/p.total;assert(rasterStrokeReveal(rows,progress,0)>0);assert.equal(rasterStrokeReveal(rows,progress,1),0);assert.equal(rasterStrokeReveal(rows,1,1),1);});
test('short Chinese strokes finish then wait through a longer spoken explanation',()=>{
 const p=writingPlan([row(1,0),row(1,1)]),cues=[{row:0,writeStart:2,writeEnd:10},{row:1,writeStart:12,writeEnd:20}];
 const firstEnd=p.segments.filter(s=>s.mainLine===0).at(-1).end/p.total;
 assert(Math.abs(rowNarrationProgress(cues,3,p)-firstEnd)<1e-9);assert.equal(rowNarrationProgress(cues,11,p),firstEnd);
 const manifest={duration:25,boards:[{page:0,start:0,eraseStart:0,writeStart:2,writeEnd:20,end:25,lineCues:cues}]};
 assert.equal(narrationFrame(manifest,2.03,p).writing,true);assert.equal(narrationFrame(manifest,3,p).writing,false);
 assert.equal(narrationFrame(manifest,12.03,p).writing,true);
});
test('Chinese bitmap metrics include font bearings and lower descenders',()=>{const g={fontSize:220,advance:220,bounds:[17,58,235,271],origin:[18,225]},a=chineseMetrics(g,44),b=chineseMetrics(g,88);assert.equal(a.actualBoundingBoxDescent,9.200000000000001);assert.equal(b.width,2*a.width);assert.equal(b.actualBoundingBoxDescent,2*a.actualBoundingBoxDescent);});
