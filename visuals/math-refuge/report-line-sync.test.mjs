import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {createHash} from 'node:crypto';
const canonical=o=>JSON.stringify(Object.fromEntries(Object.keys(o).sort().map(k=>[k,o[k]])));
const hash=o=>createHash('sha256').update(canonical(o)).digest('hex');
for(const voice of ['ye','ye-young']) test(voice+': all visible Ye main lines have reviewed speech and actual audio intervals',async()=>{
 const {pages}=JSON.parse(await fs.readFile(new URL('./assets/chalk/ye/pages.json',import.meta.url)));
 const m=JSON.parse(await fs.readFile(new URL(`./assets/audio/reports/${voice}/narration.json`,import.meta.url)));
 assert.equal(m.lineSyncVersion,1);assert.equal(m.boards.length,pages.length);
 let count=0;
 for(const b of m.boards){
  const page=pages[b.page];if(page.kind)continue;
  const source=[{title:page.title,enTitle:page.en.title},...page.boardLines];
  assert.equal(b.lineCues.length,source.length,page.title);
  b.lineCues.forEach((c,i)=>{
   assert.equal(c.row,i);assert.equal(hash(c.source),hash(source[i]),page.title+' row '+i+': exact source');
   assert.equal(c.sourceSha256,hash(source[i]));assert(c.text.length>=10);
   assert(c.audioStart<c.audioEnd&&c.writeStart<c.writeEnd);
   assert(c.writeStart>=b.writeStart&&c.writeEnd<=b.writeEnd+.001);
   if(i){const prev=b.lineCues[i-1];assert(c.writeStart>=prev.writeEnd);assert(c.audioStart>=prev.audioEnd);}
   assert(m.paragraphs.some(p=>p.page===b.page&&p.row===i&&p.text===c.text&&p.start===c.audioStart&&p.end===c.audioEnd));
   count++;
  });
  const intro=m.paragraphs.filter(p=>p.page===b.page&&p.role==='transition');assert.equal(intro.length,1);assert(intro[0].text.length<45,'short transition');
  assert.equal(b.writeEnd,b.lineCues.at(-1).writeEnd);
 }
 assert.equal(count,164);
 const parameter=m.boards[21].lineCues[4];
 assert(parameter.source.tex.startsWith('[1-\\alpha(1+o_d(1))]'));
 assert(parameter.text.includes('左边')&&parameter.text.includes('系数')&&parameter.text.includes('降权范数'));
 assert(m.boards[9].lineCues[3].source.text.includes('a=u/'));
 assert(m.boards[9].lineCues[1].text.includes('a'));
 assert(m.boards[4].lineCues[1].text.includes('偶数')&&m.boards[4].lineCues[1].text.includes('奇数'),'both cases spoken');
 assert(m.boards[25].lineCues[4].text.includes('二分之三'),'correct d^(3/2)');
});


for(const voice of ['ye','ye-young']) test(voice+': greeting starts immediately, title writing is natural and its narration waits',async()=>{
 const m=JSON.parse(await fs.readFile(new URL(`./assets/audio/reports/${voice}/narration.json`,import.meta.url))),cover=m.boards[0],intro=m.paragraphs.filter(p=>p.page===0);assert.equal(intro[0].start,0);assert.match(intro[0].text,/我是叶东/);assert.match(intro[0].text,/和黄侠合作/);assert.equal(intro[1].role,'title');assert(intro[1].start>cover.writeEnd);assert(cover.writeEnd>=12&&cover.writeEnd<=18);assert(m.pace.maxSpeechGapSeconds<=3.2);
});
