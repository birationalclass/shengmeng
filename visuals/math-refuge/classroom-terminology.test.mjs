import test from 'node:test';import assert from 'node:assert/strict';import fs from 'node:fs';import {createHash} from 'node:crypto';
const read=p=>JSON.parse(fs.readFileSync(new URL(p,import.meta.url),'utf8'));
test('board content and GitHub Algebra I courseware use the requested conjugation-orbit terminology',()=>{
 const pages=read('./assets/chalk/sylow-theorems/pages.json');assert(JSON.stringify(pages).includes('共轭轨道公式'));assert(!JSON.stringify(pages).includes('类方程'));
 for(const name of ['group-sections.js','index.html','lesson-english.js','lesson-1/lesson.js','lesson-groups/chapter-two.js','lesson-groups/exercises.js','lesson-groups/visuals.js','lesson-groups/sections/2.5.json','lesson-groups/sections/2.6.json','schedule.json']){const text=fs.readFileSync(new URL('../../courses/abstract-algebra/2026-fall/'+name,import.meta.url),'utf8');assert(!text.includes('类方程'),name);}
 const index=read('./assets/chalk/chinese36/index.json'),chars=new Set(index.glyphs.map(g=>g.char));for(const c of '共轭轨道公式')assert(chars.has(c),'new terminology glyph: '+c);
});
test('narration edits use real regenerated MP3s with valid hashes and a continuous timeline',()=>{
 const m=read('./assets/audio/courses/sylow-theorems/narration.json');assert(!JSON.stringify(m).includes('类方程'));assert(m.production.terminologyRevision.includes('7 regenerated clips'));
 for(let i=0;i<m.chapters.length;i++){const c=m.chapters[i];if(i)assert(Math.abs(m.chapters[i-1].start+m.chapters[i-1].duration-c.start)<.002,'chapter continuity '+i);if(c.src){const bytes=fs.readFileSync(new URL('./assets/audio/courses/sylow-theorems/'+c.src,import.meta.url));assert.equal(bytes.length,c.bytes);assert.equal(createHash('sha256').update(bytes).digest('hex'),c.sha256);}}
 assert(Math.abs(m.chapters.at(-1).start+m.chapters.at(-1).duration-m.duration)<.002);
 for(const b of m.boards)for(const c of b.lineCues||[])if(c.writeBeforeSpeech)assert(c.writeEnd<=c.audioStart+.001,'ink precedes explanation: '+b.page);
});
