import test from 'node:test';import assert from 'node:assert/strict';import vm from 'node:vm';import fs from 'node:fs';
import {AssetRetry} from './asset-retry.js';import {LectureClock} from './lecture-state.js';
import {drawClassroomMetadata} from './classroom-metadata.js';import {createResourceFetch} from './resource-fetch.js';
const source=fs.readFileSync(new URL('./lecture.js',import.meta.url),'utf8');
const deferred=()=>{let resolve,reject;const promise=new Promise((r,e)=>{resolve=r;reject=e;});return{promise,resolve,reject};};
const tick=()=>new Promise(r=>setImmediate(r));
function loader(){const glyph=deferred(),turns=[];let deadlineCalls=0;const canvas={width:1536,height:640,getContext:()=>({})};
 const c={options:{},generation:0,language:'zh',writingStyle:'refined',canAuthor:true,cache:new Map(),pending:new Map(),assetRetry:new AssetRetry(),pages:[{classroom:true,formulaAsset:'f.svg'}],Image:class{},document:{createElement:()=>canvas},W:1536,H:640,chineseChalk:null,createChineseChalk:async()=>({prepare:()=>glyph.promise}),chalkPageText:()=>'',preparationTurn:async()=>{turns.push(1);},prepareInlineMath:async()=>{},authoredFormula:async()=>({}),authoredContext:()=>({ctx:{},rows:r=>r}),composeChalkPage:()=>[],pageRows:new Map(),guides:new Map(),erasePlans:new Map(),erasingPlan:()=>({duration:1}),writingPlan:()=>({duration:1}),clock:new LectureClock(1),version:0,seekPinned:new Set(),pixelScale:1,withDeadline:()=>{deadlineCalls++;throw Error('old fixed page deadline');}};
 const method=source.slice(source.indexOf('  function load('),source.indexOf('  if(!disabled&&hasSelection)'));
 return{c,glyph,turns,deadlines:()=>deadlineCalls,load:vm.runInNewContext(method+';load',c)};
}
test('slow healthy glyph preparation has no 15/20/30 second wall-clock race discarding its completed board',async()=>{
 const h=loader(),job=h.load(0);await tick();assert.equal(h.c.pending.size,1);assert.equal(h.c.cache.size,0);assert.equal(h.deadlines(),0);
 h.glyph.resolve({});assert(await job);assert(h.c.cache.has(0));assert.equal(h.c.pending.size,0);
});
test('a superseded course cannot publish a page after a cooperative preparation yield',async()=>{
 const h=loader(),turn=deferred();h.c.preparationTurn=()=>turn.promise;const job=h.load(0);h.glyph.resolve({});await tick();h.c.generation++;h.c.pending.clear();turn.resolve();assert.equal(await job,null);assert.equal(h.c.cache.size,0);assert.equal(h.c.pageRows.size,0);
});
test('target board navigation releases while its MP3 is still transferring',async()=>{
 const ink=deferred(),audio=deferred(),clock=new LectureClock(12);clock.seek(4);let drawn=false,readyPromise;
 const c={disabled:false,cancelBoardWork(){},boardPreparation:null,openingDemo:null,seekRequest:0,generation:0,clock,assetRetry:{clear(){}},loadingError:null,requestedPage:null,seeking:false,seekPinned:new Set(),load:()=>ink.promise,
 voice:{manifest:{boards:Array.from({length:12},(_,page)=>({page,writeStart:page*60}))},seek:async(t,{ready})=>{readyPromise=ready;await Promise.all([ready,audio.promise]);},pause(){}},lessonBudget:{configure(){},seek(){}},omittedProofPages:new Set(),pageRows:new Map(),guides:new Map(),erasePlans:new Map(),writingPlan:()=>({}),narrationFrame:()=>({}),syncNarrationClock(){},boardSlot:p=>p%6,mix:[0,0,0],targets:[0,0,0],boardHeights:()=>[1,2],boards:Array.from({length:6},()=>({group:{position:{}}})),eraser:{userData:{}},parkedErasers:[],chalk:{},particles:[],particlePositions:{fill(){}},dustGeometry:{attributes:{position:{}}},resetWipe(){},draw:()=>{drawn=true;},version:0};
 const method=source.slice(source.indexOf('  async function seek(page,'),source.indexOf('  async function revealCurrent()'));
 const seek=vm.runInNewContext(method+';seek',c),job=seek(5,{preservePlayback:true});ink.resolve({});assert.equal(await job,true);assert(drawn);assert.equal(clock.page,5);assert.equal(c.seeking,false);assert.equal(await readyPromise,true);audio.resolve();
});
test('selection commits its clean prepared board without waiting for narration download',()=>{
 const setReport=source.slice(source.indexOf('    async setReport('),source.indexOf('    setWoodTone('));
 assert(!setReport.includes('await voicePreparation'));assert(setReport.includes('await load(0,manifest.cover)'));assert(setReport.includes('clock.startWrite()'));
});
test('all page watermarks remain at the right bottom, including exercise and lottery boards',()=>{
 for(const page of [{classroom:true},{classroom:true,exerciseBoard:true}])for(const exercise of [false,true]){
  const painted=[],ctx={save(){},restore(){},measureText:t=>({actualBoundingBoxAscent:40,actualBoundingBoxDescent:5,actualBoundingBoxRight:180}),fillText:(text,x,y)=>painted.push({text,x,y})};
  drawClassroomMetadata(ctx,page,2,'zh',{exercise,total:28});assert.equal(painted[0].text,'3 / 28');assert.equal(painted[0].x,1324);assert.equal(painted[0].y,603);
 }
});
test('back face crossbars are removed without removing the perimeter frame or board backing',()=>{
 assert(!source.includes('Rear nanmu stiffener'));assert(source.includes('Solid opaque board body'));assert(source.includes('trayHardware.createFrame(group,BOARD_W,BOARD_H)'));
});
test('continuous slow download outlives former page deadline while a real stall still aborts',async()=>{
 let timer,canceled=false;const fetcher=createResourceFetch(async src=>new Response(new ReadableStream({start(c){let n=0;timer=setInterval(()=>{c.enqueue(new Uint8Array([n++]));if(n===10){clearInterval(timer);c.close();}},8);},cancel(){canceled=true;clearInterval(timer);}})),{idleTimeout:30,totalTimeout:0});
 assert.equal((await(await fetcher('slow')).arrayBuffer()).byteLength,10);assert(!canceled);
 const stalled=createResourceFetch(async()=>new Response(new ReadableStream({cancel(){canceled=true;}})),{idleTimeout:20});await assert.rejects((await stalled('stalled')).arrayBuffer(),e=>e.name==='TimeoutError');assert(canceled);
});
