import test from 'node:test';import assert from 'node:assert/strict';
import {inkGuides,writingPlan,inkReveal,strokeReveal} from './chalk-motion.js';
import {rowNarrationProgress} from './report-voice.js';
test('sub-sample vertical ink retains a writing-clock segment before the next narration line',()=>{
 const pixels={width:40,height:24,data:new Uint8ClampedArray(40*24*4)};
 for(let y=2;y<22;y++)pixels.data[(y*40+12)*4+3]=255;
 const rows=[Object.assign([10,0,4,24],{mainLine:4}),Object.assign([20,2,12,20],{mainLine:5,strokePath:[[20,2],[32,22]]})],guides=inkGuides(pixels,rows),plan=writingPlan(rows,guides);
 assert(guides[0].inkColumns.length>0);assert(plan.segments.some(s=>s.row===0));
 const progress=rowNarrationProgress([{row:4,writeStart:1,writeEnd:3},{row:5,writeStart:12,writeEnd:14}],3.05,plan);
 assert.equal(inkReveal(rows,progress,0,guides),4);assert.deepEqual(strokeReveal(rows,progress,1,guides),[]);
});
test('a genuinely blank raster remains absent, without fabricated writing',()=>{
 const rows=[[10,0,4,24]],guides=inkGuides({width:40,height:24,data:new Uint8ClampedArray(40*24*4)},rows);assert.equal(guides[0].inkColumns.length,0);assert.equal(writingPlan(rows,guides).segments.length,0);
});
