import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {composeChalkPage} from './chalk-language.js';
import {drawChalkAnnotation} from './chalk-annotations.js';
import {writingPlan,writingPose,inkReveal,strokeReveal,erasingPlan} from './chalk-motion.js';

function context(){
  return {strokes:0,tints:0,clearRect(){},save(){},restore(){},fillRect(){this.tints++;},drawImage(){},beginPath(){},stroke(){this.strokes++;},moveTo(){},lineTo(){},fillText(){},measureText(t){return {width:[...t].length*parseFloat(this.font)*.65};}};
}
test('definition marks follow their own line, precede later content, and preserve white formula ink',async()=>{
  for(const folder of ['','hu/','ye/','duan/']){
    const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/'+folder+'pages.json',import.meta.url)));
    for(const page of pages)for(const lang of ['zh','en']){
      const ctx=context(),rows=composeChalkPage(ctx,page,0,lang,{},{deferStrokes:true});
      assert.equal(ctx.strokes,0,'No annotation strokes can leak into a formula scan');
      assert.equal(ctx.tints,0,'Framing a definition must not recolor its mathematical ink');
      if(!page.annotation)continue;
      const first=rows.findIndex(r=>r.annotation),plan=writingPlan(rows);
      const next=rows.findIndex((r,i)=>i>first&&!r.annotation);
      assert(first>0&&next>first,'There is still more page content after the local annotation');
      assert.equal(rows[first-1].formulaRow,page.annotation.row);
      assert.equal(rows[first-1].chalkColor,undefined,'Formula keeps its original chalk color');
      assert(rows.slice(first,next).every(r=>r.annotation));
      if(page.annotation.label)assert(!rows[next-1].strokePath,'A short note follows its frame');
      const start=plan.segments.find(s=>s.row===first).start/plan.total,end=plan.segments.find(s=>s.row===next).start/plan.total;
      assert.equal(inkReveal(rows,(start+end)/2,first-1),rows[first-1][2]);
      for(let row=next;row<rows.length;row++)assert.equal(inkReveal(rows,(start+end)/2,row),0,'Next content waits until this annotation is finished');
      for(let row=first;row<next;row++)if(rows[row].strokePath){
        assert.deepEqual(strokeReveal(rows,start/2,row),[],'Marking cannot precede the definition');
        assert.deepEqual(strokeReveal(rows,1,row),rows[row].strokePath);
      }
    }
  }
});

test('framed emphasis uses four rectangular sides around the selected term, with a nearby arrow',()=>{
  const target=[90,180,460,80],ctx=context();
  const rows=drawChalkAnnotation(ctx,[target],{row:0,mark:'c',focus:[.2,.25,.4,.5],label:{en:'Key definition'}},'en',{deferStrokes:true});
  const dashes=rows.filter(r=>r.strokePath).slice(0,-2),sides=new Set();
  const [left,top,width,height]=rows.focusBounds,right=left+width,bottom=top+height;
  assert(width<target[2]/2&&height<target[3],'Frame only the term, not the full equation');
  assert(dashes.length>15);
  for(const {strokePath:path} of dashes){
    const [a,b]=[path[0],path.at(-1)],length=Math.hypot(b[0]-a[0],b[1]-a[1]);
    assert(length>5&&length<22,'Short separated marks, not one continuous outline');
    const x=(a[0]+b[0])/2,y=(a[1]+b[1])/2;
    const side=y<top?'top':y>bottom?'bottom':x<left?'left':x>right?'right':null;
    assert(side,'Each dash lies outside the content on a rectangular edge');sides.add(side);
    if(side==='top'||side==='bottom')assert(Math.abs(b[1]-a[1])<2);
    else assert(Math.abs(b[0]-a[0])<2);
  }
  assert.equal(sides.size,4);
  const leader=rows.filter(r=>r.strokePath).at(-2).strokePath,tip=leader.at(-1);
  assert(tip[0]-right<12&&tip[0]>right,'Arrowhead sits next to the local frame');
  assert(Math.hypot(leader[0][0]-tip[0],leader[0][1]-tip[1])<45,'Short leader without a fixed distant margin');
  assert.equal(target.chalkColor,undefined);
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
  // v83 adds six pixels of wrist travel at either end of the occupied cell run.
  assert(plan.segments.filter(s=>s.contact).every(s=>s.a[0]>=42&&s.a[0]<=118&&s.a[1]<=70));
});
