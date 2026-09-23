import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {composeChalkPage} from './chalk-language.js';
import {drawChalkAnnotation} from './chalk-annotations.js';
import {writingPlan,writingPose,strokeReveal,erasingPlan} from './chalk-motion.js';

function context(){
  return {strokes:0,clearRect(){},save(){},restore(){},fillRect(){},drawImage(){},beginPath(){},stroke(){this.strokes++;},moveTo(){},lineTo(){},fillText(){},measureText(t){return {width:[...t].length*parseFloat(this.font)*.65};}};
}
test('all report annotations wait for complete page content and are absent from the cached base ink',async()=>{
  for(const folder of ['','hu/','ye/','duan/']){
    const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/'+folder+'pages.json',import.meta.url)));
    for(const page of pages)for(const lang of ['zh','en']){
      const ctx=context(),rows=composeChalkPage(ctx,page,0,lang,{},{deferStrokes:true});
      assert.equal(ctx.strokes,0,'No annotation strokes can leak into a formula scan');
      if(!page.annotation)continue;
      const first=rows.findIndex(r=>r.annotation),plan=writingPlan(rows);
      assert(first>0&&rows.slice(first).every(r=>r.annotation));
      assert(rows.slice(0,first).every(r=>!r.strokePath));
      assert(!rows.at(-1).strokePath,'Margin note follows the annotation strokes');
      const start=plan.segments.find(s=>s.row===first).start/plan.total;
      for(let row=first;row<rows.length;row++)if(rows[row].strokePath){
        assert.deepEqual(strokeReveal(rows,start/2,row),[],'Marking cannot start during body writing');
        assert.deepEqual(strokeReveal(rows,1,row),rows[row].strokePath);
      }
    }
  }
});

test('framed emphasis uses four rectangular sides with separate short dashes',()=>{
  const target=[90,180,460,80],ctx=context();
  const rows=drawChalkAnnotation(ctx,[target],{row:0,mark:'c',label:{en:'Key definition'}},'en',{deferStrokes:true});
  const dashes=rows.filter(r=>r.strokePath).slice(0,-2),sides=new Set();
  assert(dashes.length>30);
  for(const {strokePath:path} of dashes){
    const [a,b]=[path[0],path.at(-1)],length=Math.hypot(b[0]-a[0],b[1]-a[1]);
    assert(length>5&&length<22,'Short separated marks, not one continuous outline');
    const x=(a[0]+b[0])/2,y=(a[1]+b[1])/2;
    const side=y<180?'top':y>260?'bottom':x<90?'left':x>550?'right':null;
    assert(side,'Each dash lies outside the content on a rectangular edge');sides.add(side);
    if(side==='top'||side==='bottom')assert(Math.abs(b[1]-a[1])<2);
    else assert(Math.abs(b[0]-a[0])<2);
  }
  assert.equal(sides.size,4);
});

test('stroke reveal follows the chalk in both directions and lifts between dashes',()=>{
  const rows=[Object.assign([10,10,100,80],{strokePath:[[100,20],[100,80],[20,80]]}),Object.assign([10,90,30,10],{strokePath:[[20,95],[40,95]]})];
  const plan=writingPlan(rows);
  for(const s of plan.segments){
    const progress=(s.start+s.cost*.5)/plan.total,p=writingPose(rows,progress),shown=strokeReveal(rows,progress,s.row);
    if(s.entering){assert.deepEqual(shown,[]);assert(!p.contact);}
    else{assert(p.contact);assert.deepEqual(shown.at(-1),[p.x,p.y]);assert.equal(shown.length,s.strokePoint+2);}
    if(s.row===0)assert.deepEqual(strokeReveal(rows,progress,1),[]);
    else assert.deepEqual(strokeReveal(rows,progress,0),rows[0].strokePath);
  }
});

test('eraser wipes deferred annotation paths even outside the base ink pixels',()=>{
  const image={width:160,height:112,data:new Uint8ClampedArray(160*112*4)};
  const rows=[Object.assign([62,54,38,5],{strokePath:[[64,56],[98,57]]})],plan=erasingPlan(image,rows);
  assert(plan.segments.some(s=>s.contact),'Deferred frames are part of the wipe plan');
  assert(plan.segments.filter(s=>s.contact).every(s=>s.a[0]>=48&&s.a[0]<=112&&s.a[1]<=70));
});
