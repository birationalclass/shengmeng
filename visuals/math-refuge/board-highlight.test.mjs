import test from 'node:test';
import assert from 'node:assert/strict';
import {narrationHighlights,measuredHighlight,highlightFrame,laserPoints,laserLifetimeAlpha,HIGHLIGHT_SECONDS} from './board-highlight.js';
const row=(rect,props={})=>Object.assign(rect,{mainLine:4,...props});
const rows=[row([100,100,120,28]),row([235,105,20,16],{symbol:'≥',topLevel:true,symbolRect:[235,105,20,16]}),row([270,100,90,28]),row([365,105,16,16],{symbol:'+',topLevel:true,symbolRect:[365,105,16,16]}),row([390,96,150,34])];
const plan={segments:rows.map((_,i)=>({row:i,mainLine:4,start:i*20,end:(i+1)*20})),total:100};
const spec={id:'left',page:21,row:4,time:11,writeStart:10,writeEnd:15,pageEnd:30,side:'left',operator:'≥'};
test('laser measures the actual inequality operator and waits for the pointed ink',()=>{
 const left=measuredHighlight(spec,rows,plan),right=measuredHighlight({...spec,id:'right',side:'right'},rows,plan);
 assert.deepEqual(left.rect,[100,100,120,28]);assert.deepEqual(right.rect,[270,96,270,34]);assert.equal(left.visibleAt,11);assert.equal(right.visibleAt,15);
 assert.equal(highlightFrame([right],14.99,{page:21}),null,'future symbols stay unmarked');assert(highlightFrame([right],15.3,{page:21}));
 assert.equal(measuredHighlight(spec,[row([100,100,440,34])],plan),null,'missing relation cannot guess midpoint');
});
test('term references select entropy and exponential moment separately',()=>{
 const first=measuredHighlight({...spec,side:'right',term:0},rows,plan),second=measuredHighlight({...spec,side:'right',term:1},rows,plan);assert.deepEqual(first.rect,[270,100,90,28]);assert.deepEqual(second.rect,[390,96,150,34]);
});
test('wrong page, disabled setting, hidden boards and expired references are invisible',()=>{
 const cue=measuredHighlight(spec,rows,plan);assert.equal(highlightFrame([cue],12,{page:22}),null);assert.equal(highlightFrame([cue],12,{page:21,enabled:false}),null);assert.equal(highlightFrame([cue],12,{page:21,visible:false}),null);assert.equal(highlightFrame([cue],cue.begin+HIGHLIGHT_SECONDS,{page:21}),null);
 const a=highlightFrame([cue],cue.begin+.01,{page:21}),b=highlightFrame([cue],cue.begin+.6,{page:21}),c=highlightFrame([cue],cue.begin+3.4,{page:21});assert(a.alpha<b.alpha&&c.alpha<b.alpha);assert(a.reveal<b.reveal);assert(b.reveal===1);
 assert.equal(laserLifetimeAlpha(4),0,'pausing speech cannot keep a laser circle indefinitely');
});
test('hand-drawn contour is stable, closed, gently irregular and separated from chalk',()=>{
 const rect=[400,200,300,55],a=laserPoints(rect,3),b=laserPoints(rect,3);assert.deepEqual(a,b);assert(Math.hypot(a[0][0]-a.at(-1)[0],a[0][1]-a.at(-1)[1])<1e-9);const radii=a.map(([x,y])=>Math.hypot((x-550)/164,(y-227.5)/39.5));assert(Math.max(...radii)-Math.min(...radii)>.03);assert(Math.max(...radii)<1.15);assert(Math.min(...radii)>.85);
});
test('spoken references bind to source formula on the same board, using aligned words when present',()=>{
 const p={section:1,paragraph:7,page:1,start:100,end:140,text:'固定右边这个位置平方的权',referenceTimes:{'固定右边':.7}},m={boards:[{page:1,end:160,lineCues:[{row:2,source:{tex:'M(u)=\\sum u^2/n^2'},writeStart:40,writeEnd:50}]}],paragraphs:[p]};const [cue]=narrationHighlights(m);assert.equal(cue.row,2);assert.equal(cue.side,'right');assert.equal(cue.relation,1);assert.equal(cue.time,100.7);assert.equal(cue.timing,'aligned');assert.equal(narrationHighlights({...m,paragraphs:[{...p,page:2}]}).length,0);
});
