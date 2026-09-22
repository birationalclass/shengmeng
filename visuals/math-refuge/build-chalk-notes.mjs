// Generate local SVG chalk pages from the existing notebook, not retyped maths.
// Usage: node build-chalk-notes.mjs /absolute/path/to/mathjax-full-3.2.2
// MathJax is a build-only dependency; the deployed scene loads no math CDN.
import fs from 'node:fs/promises';
import {equationLines} from './chalk-layout.mjs';
import {chalkSVG} from './chalk-typography.js';
import {boardDiagrams,diagramSVG} from './chalk-diagrams.mjs';
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
const {outline:sections}=await import('./chalk-outline.mjs');
delete globalThis.document;
const escape=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&apos;'}[c]));
const chunks=(text,n)=>Array.from({length:Math.ceil([...text].length/n)},(_,i)=>[...text].slice(i*n,(i+1)*n).join(''));
const output=new URL('./assets/chalk/',import.meta.url);await fs.mkdir(output,{recursive:true});
const pages=[];
for(const file of await fs.readdir(output))if(/^(page|formula)-\d+\.svg$/.test(file))await fs.unlink(new URL(file,output));
for(const section of sections){
  const tex=section.tex,diagram=boardDiagrams.get(pages.length);
  const parts=equationLines(tex).map(line=>{
    const node=doc.convert(line,{display:true}),svg=adaptor.outerHTML(adaptor.tags(node,'svg')[0]);
    if(svg.includes('data-mjx-error'))throw new Error(`Bad formula: ${line}`);
    return {svg,viewBox:svg.match(/viewBox="([^"]+)"/)[1].split(/\s+/).map(Number)};
  });
  const gap=440,totalWidth=Math.max(...parts.map(p=>p.viewBox[2])),totalHeight=parts.reduce((n,p)=>n+p.viewBox[3],0)+gap*(parts.length-1);
  const viewBox=[0,0,totalWidth,totalHeight],scale=Math.min(.050,(diagram?820:1320)/totalWidth,285/totalHeight);
  const formulaAsset=`formula-${String(pages.length+1).padStart(3,'0')}.svg`;
  const w=totalWidth*scale,h=totalHeight*scale,x=92,y=140+(285-h)/2,formulaRows=[];
  let offset=0;
  const inner=parts.map(part=>{
    const [vx,vy,vw,vh]=part.viewBox;
    formulaRows.push([x-3,y+offset*scale-3,vw*scale+6,vh*scale+6]);
    const svg=part.svg.replace(/<svg[^>]*>/,`<svg x="0" y="${offset}" width="${vw}" height="${vh}" viewBox="${part.viewBox.join(' ')}">`);
    offset+=vh+gap;return svg;
  }).join('').replaceAll('currentColor','#eee9d5');
  let standalone=`<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="${totalWidth/1000*24}" height="${totalHeight/1000*24}" viewBox="${viewBox.join(' ')}">${inner}</svg>`;
  let pageX=x,pageY=y,pageW=w,pageH=h,formulaEm=viewBox[2]/1000;
  if(diagram){
    const math=(tex,cx,cy,size)=>{
      const raw=adaptor.outerHTML(adaptor.tags(doc.convert(tex,{display:false}),'svg')[0]);
      const box=raw.match(/viewBox="([^"]+)"/)[1].split(/\s+/).map(Number),dw=box[2]*size/1000,dh=box[3]*size/1000;
      return raw.replace(/<svg[^>]*>/,`<svg x="${cx-dw/2}" y="${cy-dh/2}" width="${dw}" height="${dh}" viewBox="${box.join(' ')}">`).replaceAll('currentColor','#eee9d5');
    };
    const graph=diagramSVG(diagram.kind,math).replace('<svg xmlns=', '<svg x="870" y="0" xmlns=');
    const formula=standalone.replace(/<svg[^>]*>/,`<svg x="0" y="${(320-h)/2}" width="${w}" height="${h}" viewBox="${viewBox.join(' ')}">`);
    standalone=`<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="1350" height="320" viewBox="0 0 1350 320">${formula}${graph}</svg>`;
    pageY=122.5;pageW=1350;pageH=320;formulaEm=27;
    // Main mathematics finishes first, then the diagram is drawn in short bands.
    for(let band=0;band<8;band++)formulaRows.push([x+870,pageY+band*40,480,40]);
  }
  await fs.writeFile(new URL(formulaAsset,output),standalone);
  const svg=standalone.replace(/<svg[^>]*>/,`<svg x="${pageX}" y="${pageY}" width="${pageW}" height="${pageH}" viewBox="${diagram?'0 0 1350 320':viewBox.join(' ')}">`);
  const notes=chunks(section.text||'',33);
  const page=pages.length+1,asset=`page-${String(page).padStart(3,'0')}.svg`;
  const lines=notes.slice(0,3).map((line,i)=>`<text x="88" y="${488+i*42}" font-size="36">${chalkSVG(line)}</text>`).join('');
  const body=`<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="1536" height="640" viewBox="0 0 1536 640"><g fill="#eee9d5" font-family="Kaiti SC, STKaiti, KaiTi, PingFang SC, serif"><text x="84" y="76" font-size="44" fill="#e4cf9c">${chalkSVG(section.source)}  ${chalkSVG(section.title)}</text>${svg}${lines}</g></svg>`;
  await fs.writeFile(new URL(asset,output),body);
  pages.push({...section,asset:`./assets/chalk/${asset}`,formulaAsset:`./assets/chalk/${formulaAsset}`,formulaEm,diagram:diagram||null,formulaRows,rows:[[80,22,1380,66],[80,95,0,0],[pageX-8,pageY-8,pageW+16,pageH+16],...notes.slice(0,3).map((_,i)=>[80,452+i*42,1380,42])]});
}
await fs.writeFile(new URL('pages.json',output),JSON.stringify({source:'../../study/spectral/',generator:'MathJax 3.2.2 SVG / original notebook exports',pages},null,2)+'\n');
await fs.copyFile(path.join(root,'LICENSE'),new URL('MATHJAX-LICENSE.txt',output));
console.log(`Generated ${pages.length} chalk pages from the spectral notebook.`);
