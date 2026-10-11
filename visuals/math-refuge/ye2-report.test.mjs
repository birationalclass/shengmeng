import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {createHash} from 'node:crypto';
import {REPORTS} from './report-catalog.js';
import {buildReportPlan} from './report-settings.js';
const read=async p=>JSON.parse(await fs.readFile(new URL(p,import.meta.url)));
const canonical=o=>JSON.stringify(Object.fromEntries(Object.keys(o).sort().map(k=>[k,o[k]])));
const hash=o=>createHash('sha256').update(canonical(o)).digest('hex');
test('report2 is independently selectable and uses actual bright audio, preserving report1',()=>{
 const r=REPORTS.find(r=>r.id==='ye2'),old=REPORTS.find(r=>r.id==='ye');assert.equal(r.label,'YE dong 报告2');assert.equal(r.basedOn,'ye');assert.notEqual(r.manifest,old.manifest);assert.notEqual(r.narration.manifest,old.narration.manifest);assert.match(r.narration.label,/年轻明亮/);assert.equal(buildReportPlan({},r).recommendation.route,'example');assert.equal(REPORTS.filter(r=>r.id==='ye2').length,1);
});
test('the finite sequence gives quotient 2, an upper bound rather than a sharpness claim',async()=>{
 const u=[0,1,0,0],E=u.slice(1).reduce((s,v,i)=>s+(v-u[i])**2,0),M=u.slice(1).reduce((s,v,i)=>s+v*v/(i+1)**2,0);assert.equal(E,2);assert.equal(M,1);assert.equal(E/M,2);assert(E>=M/4);const {pages}=await read('./assets/chalk/ye2/pages.json');assert.equal(pages[1].boardLines.length,5);assert.equal(pages[1].en.source,'EXAMPLE');assert.match(pages[1].text,/只给上界/);assert.match(pages[1].readingText,/不是极值|不达到/);
});
test('report2 has real per-board audio, a brief title, reviewed row cues and no long gaps',async()=>{
 const {pages}=await read('./assets/chalk/ye2/pages.json'),m=await read('./assets/audio/reports/ye2/narration.json');assert.equal(m.boards.length,31);assert.equal(m.chapters.length,31);assert.equal(pages.filter(p=>!p.kind).length,29);assert(m.duration>54*60&&m.duration<57*60);assert(m.pace.maxSpeechGapSeconds<=3.2);
 const first=m.paragraphs.filter(p=>p.page===0);assert.equal(first.length,2);assert.equal(first[0].start,0);assert.match(first[0].text,/我是叶东/);assert.match(first[0].text,/和黄侠合作/);assert(first[1].start>m.boards[0].writeEnd);assert(m.boards[0].writeEnd>=12);assert(m.chapters[0].duration<25);assert(!first.some(p=>/熵|Fourier|傅里叶|集中/.test(p.text)));
 let end=0,rows=0;
 for(let i=0;i<pages.length;i++){
  const p=pages[i],b=m.boards[i],c=m.chapters[i];assert.equal(c.board,i);assert(Math.abs(c.start-end)<.002);const bytes=await fs.readFile(new URL('./assets/audio/reports/ye2/'+c.src,import.meta.url));assert.equal(bytes.length,c.bytes);assert.equal(createHash('sha256').update(bytes).digest('hex'),c.sha256);end=c.start+c.duration;assert(b.end<=end+.002);
  if(p.kind)continue;assert(p.mainLineCount>=5&&p.mainLineCount<=6);assert(p.boardLines.some(l=>l.text),'interleave actual explanation');assert.equal(b.lineCues.length,p.boardLines.length+1);const src=[{title:p.title,enTitle:p.en.title},...p.boardLines];
  for(const [j,cue] of b.lineCues.entries()){assert.equal(cue.sourceSha256,hash(src[j]));assert.equal(cue.row,j);assert(cue.audioStart<cue.audioEnd);assert(cue.writeStart<cue.writeEnd);assert(cue.writeEnd<=b.writeEnd+.001);assert(m.paragraphs.some(q=>q.page===i&&q.row===j&&q.text===cue.text&&q.start===cue.audioStart&&q.end===cue.audioEnd));rows++;}
 }
 assert.equal(rows,170);assert(Math.abs(end-m.duration)<.002);assert.equal(m.production.rewrittenParagraphs,21);assert.equal(m.production.retainedParagraphs,235);assert.equal(m.cachePolicy,'current-and-next-board');assert(m.chapters.some(c=>c.src.startsWith('../ye-young/')),'unchanged audio reused honestly');
});
test('report2 keeps the verified source mathematics and leaves both original speech manifests intact',async()=>{
 const a=(await read('./assets/chalk/ye/pages.json')).pages,b=(await read('./assets/chalk/ye2/pages.json')).pages;for(let i=2;i<b.length-1;i++){assert.equal(b[i].title,a[i-1].title);assert.deepEqual(b[i].boardLines,a[i-1].boardLines);}
 const plan=await read('./assets/audio/reports/ye2/production-plan.json');for(const [path,expected] of Object.entries(plan.retainedOriginalSHA256)){const bytes=await fs.readFile(new URL(path,import.meta.url));assert.equal(createHash('sha256').update(bytes).digest('hex'),expected);}
});
