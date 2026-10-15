import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import vm from 'node:vm';
import {LectureClock} from './lecture-state.js';
const source=readFileSync(new URL('./lecture.js',import.meta.url),'utf8');
function fixture(kind){
 const calls=[],clock=new LectureClock(28);clock.startWrite();
 const context={options:{},disabled:false,version:0,playing:false,clock,
  openingDemo:{phase:'waiting',narrated:true},activeReport:{id:'sylow-theorems',kind},pages:[{}],
  boards:Array.from({length:6},()=>({})),draw:(index,preparing)=>calls.push(['draw',index,preparing]),
  programScreen:{select:report=>calls.push(['program',report.id])},setReportState(){},
  voice:{pause:()=>calls.push(['pause']),select:(report,options)=>{calls.push(['voice',report.id,options.autoplay]);return new Promise(()=>{});}},
  voiceReport:report=>report};
 const start=source.indexOf('    beginOpening(reduced=false){'),end=source.indexOf('    finishOpening,',start);
 const staticPage=source.match(/  function staticPage\(\)[^\n]+/)[0];
 const api=vm.runInNewContext(staticPage+'\n({'+source.slice(start,end)+'})',context);
 api.setReport=(id,options)=>{calls.push(['report',id,options.autoplay]);return 'report-start';};
 return {api,context,calls};
}
test('classroom arrival displays the full paused cover before any audio request resolves',()=>{
 const {api,context,calls}=fixture('classroom');assert.equal(api.beginOpening(),true);
 assert.equal(context.clock.page,0);assert.equal(context.clock.phase,'hold');
 assert.equal(context.clock.slots[context.clock.active].progress,1);
 assert.equal(context.playing,false);assert.equal(context.openingDemo,null);
 assert.equal(calls.filter(c=>c[0]==='draw'&&c[2]===true).length,6);
 assert.deepEqual(calls.find(c=>c[0]==='voice'),['voice','sylow-theorems',false]);
 assert(calls.findIndex(c=>c[0]==='draw')<calls.findIndex(c=>c[0]==='voice'));
 assert(!calls.some(c=>c[0]==='report'));assert.equal(api.beginOpening(),false);
});
test('report openings retain their existing automatic narrated start',()=>{
 const {api,calls}=fixture('report');assert.equal(api.beginOpening(),'report-start');
 assert.deepEqual(calls,[['report','sylow-theorems',true]]);
});
