import test from 'node:test';import assert from 'node:assert/strict';import fs from 'node:fs';
test('the class equation board defines action, stabilizer and indexed representatives before the sum',()=>{
 const pages=JSON.parse(fs.readFileSync(new URL('./assets/chalk/sylow-theorems/pages.json',import.meta.url))).pages,p=pages.find(p=>p.expositionBoard);assert(p);assert.equal(p.mainLineCount,6);
 assert(p.exerciseLines[0].text.includes('g·x=gxg⁻¹'));assert(p.exerciseLines[1].text.includes('稳定子'));assert(p.exerciseLines[2].text.includes('单点'));assert(p.exerciseLines[3].text.includes('i=1,…,r'));assert(p.exerciseLines[4].tex.includes('sum_{i=1}^{r}'));
 const m=JSON.parse(fs.readFileSync(new URL('./assets/audio/courses/sylow-theorems/narration.json',import.meta.url))),b=m.boards[pages.indexOf(p)];assert.equal(b.lineCues.length,6);assert(b.lineCues.at(-1).audioStart>=b.lineCues.at(-2).audioEnd);
});
test('independent S3 conjugation orbits satisfy the displayed stabilizer index and partition equation',()=>{
 const perms=[];for(let a=0;a<3;a++)for(let b=0;b<3;b++)for(let c=0;c<3;c++)if(new Set([a,b,c]).size===3)perms.push([a,b,c]);
 const mul=(g,x)=>x.map(v=>g[v]),inv=g=>g.map((_,i)=>g.indexOf(i)),key=g=>g.join(''),same=(a,b)=>key(a)===key(b),left=new Set(perms.map(key)),sizes=[];let center=0;
 while(left.size){const x=perms.find(g=>left.has(key(g))),orbit=new Set(perms.map(g=>key(mul(mul(g,x),inv(g))))),stabilizer=perms.filter(g=>same(mul(g,x),mul(x,g)));assert.equal(orbit.size,perms.length/stabilizer.length);for(const k of orbit)left.delete(k);if(orbit.size===1)center++;else sizes.push(orbit.size);}
 assert.equal(center,1);assert.deepEqual(sizes.sort(),[2,3]);assert.equal(center+sizes.reduce((a,b)=>a+b,0),6);
});
