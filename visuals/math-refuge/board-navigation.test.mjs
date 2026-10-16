import test from 'node:test';import assert from 'node:assert/strict';import vm from 'node:vm';import {readFileSync} from 'node:fs';import {LectureClock} from './lecture-state.js';
const source=readFileSync(new URL('./lecture.js',import.meta.url),'utf8');
const seekSource=source.slice(source.indexOf('  async function seek(page,'),source.indexOf('  async function revealCurrent()'));
function harness(){let release,reject;const ready=new Promise((r,e)=>{release=r;reject=e;}),events=[],clock=new LectureClock(12);clock.seek(4);
 const c={disabled:false,cancelBoardWork(){},openingDemo:null,seekRequest:0,generation:0,clock,requestedPage:null,seeking:false,seekPinned:new Set(),load:()=>ready,voice:{manifest:{boards:Array.from({length:12},(_,page)=>({page,writeStart:page*60}))},async seek(time,{ready}){await ready;events.push('resume');},pause(){}},lessonBudget:{configure(){},seek(){}},pageRows:new Map(),guides:new Map(),erasePlans:new Map(),writingPlan:()=>({}),boardSlot:p=>p%6,narrationFrame:()=>({}),syncNarrationClock:clock=>{clock.slots[clock.active].progress=0;},omittedProofPages:new Set(),mix:[0,0,0],targets:[0,0,0],boardHeights:()=>[1,2],boards:Array.from({length:6},()=>({group:{position:{}},last:'',wet:null})),eraserReturn:null,eraserPickup:null,eraser:{userData:{}},parkedErasers:[],chalk:{},previousTip:null,particles:[],particlePositions:{fill(){}},dustGeometry:{attributes:{position:{}}},resetWipe(){},draw:i=>events.push('draw:'+clock.slots[i].page),version:0,loadingError:null};
 c.assetRetry={clear(){}};c.boardPreparation=null;
 return {c,clock,events,release,reject,seek:vm.runInNewContext(seekSource+';seek',c)};
}
test('fifth-to-sixth board waits for assets, commits the sixth physical slot, then resumes',async()=>{
 const h=harness(),job=h.seek(5,{preservePlayback:true});assert(h.c.seeking);assert.equal(h.clock.page,4);assert.equal(h.events.length,0);
 h.release();assert.equal(await job,true);assert.equal(h.clock.page,5);assert.equal(h.clock.slots[5].page,5);assert.equal(h.clock.slots[5].progress,0,'navigation starts at its writing cue without a completed preview');assert(h.events.indexOf('draw:5')<h.events.indexOf('resume'));assert(!h.c.seeking);
});
test('failed board preparation keeps the previous board and releases navigation for retry',async()=>{
 const h=harness(),job=h.seek(5);h.reject(Error('download failed'));await assert.rejects(job,/download failed/);assert.equal(h.clock.page,4);assert.equal(h.events.length,0);assert(!h.c.seeking);
});
test('rapid next clicks commit only the latest page across a six-board reuse boundary',async()=>{
 const h=harness(),first=h.seek(5),second=h.seek(6);h.release();assert.equal(await first,false);assert.equal(await second,true);assert.equal(h.clock.page,6);assert.equal(h.clock.slots[0].page,6);assert(!h.c.seeking);
});
test('same-column automatic framing remains fixed while boards move in their two tracks',()=>{
 const start=source.indexOf('    cameraView(aspect,fov=57)'),end=source.indexOf('\n',start),method=source.slice(start,end).trim().replace(/,$/,'');
 const c={boardCameraFrame:(a,f,z,o)=>o,cameraZoom:0,clock:{active:0},BOARD_LAYOUT:{low:1.835},BOARD_MOUNT_OFFSET:-.595,isCrystalScheme:()=>false,trayHardware:{tone:'pale'},THREE:{Vector3:class{}},scene:{localToWorld:v=>v}};
 const api=vm.runInNewContext('({'+method+'})',c),a=api.cameraView(16/9);c.clock.active=1;const b=api.cameraView(16/9);assert.equal(a.boardY,b.boardY);assert.equal(a.boardZ,b.boardZ);assert.equal(a.column,b.column);
});
test('a failed historical page cannot block a healthy destination',async()=>{
 const h=harness();h.c.load=page=>page===2?Promise.reject(Error('old page offline')):Promise.resolve({});
 assert.equal(await h.seek(6),true);assert.equal(h.clock.page,6);assert(!h.c.seeking);
});
