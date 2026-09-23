import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {composeChalkPage} from './chalk-language.js';
test('all 124 bilingual boards have complete prose and deterministic, bounded annotations',async()=>{
  let count=0,marked=0;
  const coverage=JSON.parse(await fs.readFile(new URL('./assets/fonts/chalk-coverage.json',import.meta.url)));
  for(const folder of ['','hu/','ye/','duan/']){
    const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/'+folder+'pages.json',import.meta.url)));
    for(const [index,page] of pages.entries()){
      count++;if(!page.kind){marked++;assert(page.annotation?.label.zh&&page.annotation?.label.en);}
      for(const lang of ['zh','en']){
        assert(!/本文|文中|原文|the paper|paper’s/i.test(page[lang==='en'?'en':'text']?.text|| (lang==='zh'?page.text:'')));
        const calls=[];const ctx={clearRect(){},save(){},restore(){},fillRect(){},drawImage(){},beginPath(){},stroke(){},moveTo(x,y){calls.push([x,y]);},lineTo(x,y){calls.push([x,y]);},fillText(t,x,y){calls.push([t,x,y]);},measureText(t){return {width:[...t].length*parseFloat(this.font)*.65};}};
        const rows=composeChalkPage(ctx,page,index,lang,{}),first=JSON.stringify(calls);calls.length=0;
        composeChalkPage(ctx,page,index,lang,{});assert.equal(JSON.stringify(calls),first,'No random stroke jitter');
        for(const [x,y,w,h] of rows)assert(x>=0&&y>=0&&x+w<=1536&&y+h<=640,'No clipped writing');
        if(page.annotation)for(const c of page.annotation.label.zh)if(/[\u3400-\u9fff]/.test(c))assert(coverage.characters.includes(c));
      }
    }
  }
  assert.equal(count,124);assert.equal(marked,116);
});
