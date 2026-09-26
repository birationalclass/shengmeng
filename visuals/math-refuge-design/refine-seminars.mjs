import fs from 'node:fs/promises';
import {refineSeminarPage,wording} from './seminar-editorial.js';
import {chalkSVG} from './chalk-typography.js';
for(const id of ['meng','hu','ye','duan']){
  const dir=new URL('./assets/chalk/'+(id==='meng'?'':id+'/'),import.meta.url);
  const manifest=JSON.parse(await fs.readFile(new URL('pages.json',dir),'utf8'));
  manifest.pages=manifest.pages.map((page,index)=>refineSeminarPage(page,id,index));
  await fs.writeFile(new URL('pages.json',dir),JSON.stringify(manifest,null,2)+'\n');
  for(const page of manifest.pages){
    if(page.kind)continue;
    const file=new URL(page.asset,import.meta.url),svg=await fs.readFile(file,'utf8');
    const chunks=Array.from({length:Math.ceil([...page.text].length/33)},(_,i)=>[...page.text].slice(i*33,(i+1)*33).join(''));
    let i=0;const revised=svg.replace(/<text x="88" y="(?:488|544|600)" font-size="36">[\s\S]*?<\/text>/g,()=>`<text x="88" y="${488+i*56}" font-size="36">${chalkSVG(chunks[i++]||'')}</text>`);
    if(revised!==svg)await fs.writeFile(file,revised);
  }
  console.log(id,manifest.pages.length,'pages reviewed');
}
for(const file of ['chalk-outline.mjs','hu-report-outline.mjs','ye-report-outline.mjs','duan-report-outline.mjs']){
  const url=new URL(file,import.meta.url);let source=await fs.readFile(url,'utf8');
  for(const [a,b] of wording)source=source.replaceAll(a,b);
  await fs.writeFile(url,source);
}
