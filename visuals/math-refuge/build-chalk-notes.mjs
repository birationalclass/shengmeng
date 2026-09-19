// Generate local SVG chalk pages from the existing notebook, not retyped maths.
// Usage: node build-chalk-notes.mjs /absolute/path/to/mathjax-full-3.2.2
// MathJax is a build-only dependency; the deployed scene loads no math CDN.
import fs from 'node:fs/promises';
import path from 'node:path';
import {createRequire} from 'node:module';
const require=createRequire(import.meta.url),root=process.argv[2];
if(!root)throw new Error('Provide the extracted mathjax-full 3.2.2 package directory');
const {mathjax}=require(path.join(root,'js/mathjax.js'));
const {TeX}=require(path.join(root,'js/input/tex.js'));
const {SVG}=require(path.join(root,'js/output/svg.js'));
const {liteAdaptor}=require(path.join(root,'js/adaptors/liteAdaptor.js'));
const {RegisterHTMLHandler}=require(path.join(root,'js/handlers/html.js'));
require(path.join(root,'js/input/tex/ams/AmsConfiguration.js'));
require(path.join(root,'js/input/tex/newcommand/NewcommandConfiguration.js'));
require(path.join(root,'js/input/tex/configmacros/ConfigMacrosConfiguration.js'));
const adaptor=liteAdaptor();RegisterHTMLHandler(adaptor);
const doc=mathjax.document('',{InputJax:new TeX({packages:['base','ams','newcommand','configmacros'],macros:{vbelongs:'\\in'},formatError:(_jax,error)=>{throw error;}}),OutputJax:new SVG({fontCache:'none'})});
// The notebook's proof-dialog module registers an event listener on import.
// No UI is executed during this data-only extraction.
globalThis.document={addEventListener(){}};
const {lessons,convergence,totalCohomology}=await import('../../study/spectral/content.js');
const {hodgeContent,hodgeTitles}=await import('../../study/spectral/hodge.js');
const {lerayContent,lerayTitles}=await import('../../study/spectral/leray.js');
delete globalThis.document;
const sections=[...lessons.map((p,i)=>({...p,source:`基础 ${i+1}`})),{...totalCohomology,source:'总上同调'},...convergence.slice(0,4).map((p,i)=>({...p,source:`收敛 ${i+1}`})),
 ...hodgeContent.f.map((tex,i)=>({title:hodgeTitles[i][0],f:[tex],source:`Hodge 3.${i+1}`,text:i>=4?'假设 X 为紧 Kähler 流形；典范分裂需要额外的 ∂∂̄ 条件。':'设 X 为紧复流形。列滤过的稳定项识别总上同调的关联分次。'})),
 ...lerayContent.f.map((tex,i)=>({title:lerayTitles[i][0],f:[tex],source:`Leray 4.${i+1}`,text:i===13?'应用条件：特征零，射影双有理态射，X 光滑；结合笔记中的消失定理。':i===14?'有理奇点：特征零，X 正规，π 为解消。详细假设与证明见原笔记。':'f : X → Y 为概形态射；在模层范畴中取内射分解。详细构造见原笔记。'}))];
const escape=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&apos;'}[c]));
const chunks=(text,n)=>Array.from({length:Math.ceil([...text].length/n)},(_,i)=>[...text].slice(i*n,(i+1)*n).join(''));
const output=new URL('./assets/chalk/',import.meta.url);await fs.mkdir(output,{recursive:true});
const pages=[];
for(const section of sections)for(const [formulaIndex,tex] of section.f.entries()){
  const node=doc.convert(tex,{display:true});let svg=adaptor.outerHTML(adaptor.tags(node,'svg')[0]);
  if(svg.includes('data-mjx-error'))throw new Error(`Bad formula: ${tex}`);
  const viewBox=svg.match(/viewBox="([^"]+)"/)[1].split(/\s+/).map(Number);
  const width=1360,height=260,scale=Math.min(width/viewBox[2],height/viewBox[3]);
  const w=viewBox[2]*scale,h=viewBox[3]*scale,x=(1536-w)/2,y=155+(height-h)/2;
  svg=svg.replace(/<svg[^>]*>/,`<svg x="${x}" y="${y}" width="${w}" height="${h}" viewBox="${viewBox.join(' ')}" overflow="visible">`).replaceAll('currentColor','#eee9d5');
  const title=chunks(section.title,28),notes=chunks(section.text||'',43);
  const page=pages.length+1,asset=`page-${String(page).padStart(3,'0')}.svg`;
  const lines=notes.slice(0,3).map((line,i)=>`<text x="88" y="${462+i*43}" font-size="31">${escape(line)}</text>`).join('');
  const body=`<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="1536" height="640" viewBox="0 0 1536 640"><g fill="#eee9d5" font-family="Kaiti SC, STKaiti, KaiTi, PingFang SC, serif"><text x="84" y="70" font-size="46" fill="#e4cf9c">${escape(title[0])}</text><text x="88" y="119" font-size="26" fill="#aac8b9">${escape(section.source)} · ${formulaIndex+1}/${section.f.length}${title[1]?' · '+escape(title[1]):''}</text>${svg}${lines}<text x="88" y="611" font-size="23" fill="#9dbbab">孟晟 · 谱序列学习笔记 / ${page}</text></g></svg>`;
  await fs.writeFile(new URL(asset,output),body);
  pages.push({title:section.title,source:section.source,tex,text:section.text||'',asset:`./assets/chalk/${asset}`,rows:[[80,25,1380,56],[80,91,1380,34],[x-8,y-8,w+16,h+16],...notes.slice(0,3).map((_,i)=>[80,432+i*43,1380,42])]});
}
await fs.writeFile(new URL('pages.json',output),JSON.stringify({source:'../../study/spectral/',generator:'MathJax 3.2.2 SVG / original notebook exports',pages},null,2)+'\n');
await fs.copyFile(path.join(root,'LICENSE'),new URL('MATHJAX-LICENSE.txt',output));
console.log(`Generated ${pages.length} chalk pages from the spectral notebook.`);
