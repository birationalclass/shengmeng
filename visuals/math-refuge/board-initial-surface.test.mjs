import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import vm from 'node:vm';
import {boardContentJump} from './board-transition.js';
// Exercise the production allocation and paint functions, including the old
// blank -> cover transition which captured a transparent canvas before entry.
const source=readFileSync(new URL('./lecture.js',import.meta.url),'utf8');
function fixture(){
 const uploads=[];
 function canvas(){const c={width:1536,height:640,color:null};c.getContext=()=>c.ctx??={fillStyle:null,fillRect(){c.color=this.fillStyle;},drawImage(image){c.color=image.color;delete c.countdown;},save(){},restore(){},fillText(text){c.countdown=text;}};return c;}
 const boards=Array.from({length:6},()=>({group:{children:[{material:{}}]},canvas:null,last:'blank',content:{page:-1,progress:0,available:false},inkBlend:{value:1},previousInk:{value:null},fadeAge:1}));
 const context={boards,uploads,W:1536,H:640,grain:{color:'#193d33'},dust:{color:'#193d33'},pixelScale:1,renderer:{capabilities:{getMaxAnisotropy:()=>16}},document:{createElement:canvas},THREE:{CanvasTexture:class{constructor(c){this.image=c;this.initialColor=c.color;uploads.push(this);}},SRGBColorSpace:'srgb'},inkCanvas(){const c=canvas();return [c,c.getContext('2d')];},contentFadeQueue:[],clock:{slots:Array.from({length:6},(_,i)=>({page:i===0?0:-1,progress:0})),phase:'write'},cache:new Map(),options:{isActive:()=>true},renderActive:false,hydrating:false,stored:false,storageProgress:0,boardContentJump,effectTime:0,language:'en'};
 context.activeReport={kind:'report'};context.voice={state:{phase:'paused',activity:null}};context.drawClassroomActivity=(ctx,a)=>{ctx.fillStyle='exercise:'+Math.ceil(a.remaining);ctx.fillRect(0,0,1536,640);return{sheetIndex:0,eraseRows:[]};};
 Object.assign(context,{translating:false,hasSelection:true,pages:[{rows:[],period:1}],openingDemo:null,boardInkScale:()=>1,omittedProofPages:new Set(),currentExercise:()=>context.voice.state.activity,exerciseFrames:new Map(),exerciseEraseKeys:new Map(),erasePlans:new Map(),erasingPlan:()=>({}),paintBackground(ctx,w,h){ctx.fillStyle='#193d33';ctx.fillRect(0,0,w,h);}});
 context.SCREEN_MONO='monospace';context.clock.active=0;context.clock.page=0;
 const start=source.indexOf('  function ensureInk('),end=source.indexOf('  function positionTool(',start);
 const api=vm.runInNewContext(source.slice(start,end)+'\n({ensureInk,draw})',context);return {api,context,boards,uploads};
}
test('new diffuse and roughness canvases are opaque before texture creation or binding',()=>{
 const {api,boards,uploads}=fixture();api.ensureInk(boards[0]);assert.equal(uploads[0].initialColor,'#193d33');assert.equal(uploads[1].initialColor,'white');assert.equal(boards[0].group.children[0].material.map.image.color,'#193d33');
});
test('offscreen opening preparation paints all six surfaces without a queued fade from blank',()=>{
 const {api,boards,context}=fixture();for(let i=0;i<6;i++){api.ensureInk(boards[i]);api.draw(i,true);assert.equal(boards[i].canvas.color,'#193d33');assert.equal(boards[i].inkBlend.value,1);assert.equal(boards[i].fadeAge,1);}
 assert.equal(context.contentFadeQueue.length,0);
});
test('visible content discontinuities retain an opaque previous surface',()=>{
 const {api,boards,context}=fixture();context.renderActive=true;api.ensureInk(boards[0]);api.draw(0);assert.equal(context.contentFadeQueue.length,1);assert.equal(boards[0].inkBlend.value,0);assert.equal(boards[0].previousInk.value.image.color,'#193d33');
});

test('physical exercise countdown repaints the current opaque board and clears on feedback',()=>{
 const {api,boards,context}=fixture();context.renderActive=true;context.activeReport.kind='classroom';context.SCREEN_MONO='monospace';context.clock.active=0;context.clock.page=0;context.clock.phase='hold';context.clock.slots[0].progress=1;context.voice.state.activity={page:0,start:10,remaining:9.5,activityType:'exercise'};
 context.pages[0]={rows:[],period:1,exerciseBoard:true,exerciseLines:[],questionLineCount:0};context.voice.state.time=10;context.voice.manifest={boards:[{page:0,end:100}],chapters:[{page:0,start:10,duration:30,activityType:'exercise'}]};context.studentLottery={view:()=>({key:'steady'})};context.drawStudentLottery=()=>{};context.drawClassroomMetadata=()=>{};context.pageRows=new Map();context.cache.set(0,{color:'#193d33'});
 api.draw(0);assert.equal(boards[0].canvas.countdown,'0:10');context.voice.state.activity.remaining=8.9;api.draw(0);assert.equal(boards[0].canvas.countdown,'0:09');context.voice.state.activity=null;api.draw(0);assert.equal(boards[0].canvas.countdown,undefined);assert.equal(boards[0].canvas.color,'#193d33');
});
