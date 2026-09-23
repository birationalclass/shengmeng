import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {composeChalkPage} from './chalk-language.js';
import {KM_SECTIONS} from './km-seminar-outline.mjs';
import {KM_PROOFS} from './km-proof-boards.mjs';
test('every KM section has a scoped worked argument and bilingual non-overlapping sequential ink',async()=>{
 const coverage=JSON.parse(await fs.readFile(new URL('./assets/fonts/chalk-coverage.json',import.meta.url)));
 const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/km/pages.json',import.meta.url)));
 assert.equal(KM_PROOFS.size,38);
 const ctx={clearRect(){},drawImage(){},fillText(){},measureText(t){return {width:[...t].length*parseFloat(this.font)*.65};}};
 for(const part of KM_SECTIONS){
  const body=pages.slice(part.start+1,part.end);assert(body.some(p=>p.proof?.scope&&p.proof?.inputs));
  assert(body.every(p=>p.section===part.id));
 }
 for(const p of pages)for(const language of ['zh','en']){
  if(p.kind)continue;
  const rows=composeChalkPage(ctx,p,0,language,{});
  for(const [i,a] of rows.entries()){
   assert(a[0]>=0&&a[1]>=0&&a[0]+a[2]<=1536&&a[1]+a[3]<=640,p.title+' stays on the board');
   for(const b of rows.slice(i+1))assert(a[0]+a[2]<=b[0]||b[0]+b[2]<=a[0]||a[1]+a[3]<=b[1]||b[1]+b[3]<=a[1],p.title+' reveal rectangles must not overlap');
  }
  if(p.layout==='flow'){
   assert.deepEqual(rows.filter(r=>r.formulaRow!==undefined).map(r=>r.formulaRow),p.formulaRows.map((_,i)=>i));
   for(const l of p.flowLabels)for(const c of l.text)if(/[\u3400-\u9fff]/.test(c))assert(coverage.characters.includes(c),'Missing glyph '+c);
   if(p.proof)assert(p.blocks.length>=3,'A proof is a sequence of justified steps');
  }
 }
});
