import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {explainedFlow} from './flow-explanation.js';
import {conciseEnglish} from './board-explanations.js';
import {composeChalkPage} from './chalk-language.js';

test('physical flow boards include complete spoken explanations and preserve every formula in order',async()=>{
  const coverage=JSON.parse(await fs.readFile(new URL('./assets/fonts/chalk-coverage.json',import.meta.url)));
  let explained=0;
  const clean=s=>s.replace(/\s/g,'');
  const ctx={clearRect(){},drawImage(){},fillText(){},measureText(t){return {width:[...t].length*parseFloat(this.font)*.65};}};
  for(const folder of ['','hu/','ye/','duan/','km/']){
    const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/'+folder+'pages.json',import.meta.url)));
    for(const page of pages.filter(p=>p.layout==='flow'))for(const language of ['zh','en']){
      const items=explainedFlow(page,language,(t,s)=>[...t].length*s*.65);
      assert.deepEqual(items.filter(i=>i.source).map(i=>i.index),page.formulaRows.map((_,i)=>i));
      if(!page.proof){
        const expected=language==='en'?(conciseEnglish.get(page.title)?.join('')||page.en.text):page.text;
        const actual=items.filter(i=>i.role==='explanation').map(i=>i.text).join('');
        assert.equal(clean(actual),clean(expected),page.title+': no explanation silently disappears');explained++;
        if(language==='zh')for(const c of actual)if(/[\u3400-\u9fff]/.test(c))assert(coverage.characters.includes(c),'Missing glyph '+c);
      }
      const rows=composeChalkPage(ctx,page,0,language,{});
      for(const [i,a] of rows.entries()){
        assert(a[0]>=0&&a[1]>=0&&a[0]+a[2]<=1536&&a[1]+a[3]<=640,page.title);
        for(const b of rows.slice(i+1))assert(a[0]+a[2]<=b[0]||b[0]+b[2]<=a[0]||a[1]+a[3]<=b[1]||b[1]+b[3]<=a[1],page.title+': overlapping reveal');
      }
    }
  }
  assert(explained>300);
});
