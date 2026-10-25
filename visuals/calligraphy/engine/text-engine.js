import {cursiveGlyphs} from '../cursive-glyphs.js?v=17';
import {runningGlyphs} from '../running-glyphs.js?v=17';
import * as T from '../vendor/three.module.js';
import {catalog} from './catalog.js';
import {availableCharacters} from './coverage.js';
import {sculptAutomaticGlyph} from './auto-detail.js';

const bundles=new Map(),derived=new Map();
export function cleanText(value){
 const text=String(value).replace(/\s+/gu,'').normalize('NFC'),chars=[...text];
 if(!chars.length)throw Error('请先输入要写的汉字。');
 if(chars.length>8)throw Error('一次最多写 8 个汉字。');
 if(chars.some(c=>!/^\p{Script=Han}$/u.test(c)))throw Error('请输入汉字，可去掉数字、字母和标点后再写。');
 return text;
}
export async function loadCharacter(char){
 if(!availableCharacters.has(char))throw Error(`字库暂无「${char}」。`);
 const key=(char.codePointAt(0)>>8).toString(16);
 if(!bundles.has(key))bundles.set(key,fetch(`data/${key}.json`).then(r=>{if(!r.ok)throw Error(`字库暂无「${char}」。`);return r.json();}).catch(error=>{bundles.delete(key);throw error;}));
 const data=(await bundles.get(key))[char];if(!data)throw Error(`字库暂无「${char}」。`);return data;
}

// Flatten only the five SVG commands present in the pinned data package.
// Keeping this independent of the DOM also lets the geometry be audited in Node.
export function outlinePolygons(path){
 const tokens=path.match(/[MLQCZ]|[-+]?(?:\d*\.\d+|\d+\.?\d*)(?:e[-+]?\d+)?/gi)||[];
 let at=0,command='',point=[0,0],polygon=null;const polygons=[];
 const read=()=>{const value=Number(tokens[at++]);if(!Number.isFinite(value))throw Error('字形轮廓数据不完整。');return value;};
 const append=p=>{polygon.push(p);point=p;};
 while(at<tokens.length){
  if(/^[MLQCZ]$/i.test(tokens[at]))command=tokens[at++].toUpperCase();
  if(command==='M'){point=[read(),read()];polygon=[point];polygons.push(polygon);command='L';}
  else if(command==='L')append([read(),read()]);
  else if(command==='Q'){const a=point,b=[read(),read()],c=[read(),read()];for(let j=1;j<=16;j++){const t=j/16,q=1-t;append([q*q*a[0]+2*q*t*b[0]+t*t*c[0],q*q*a[1]+2*q*t*b[1]+t*t*c[1]]);}}
  else if(command==='C'){const a=point,b=[read(),read()],c=[read(),read()],d=[read(),read()];for(let j=1;j<=20;j++){const t=j/20,q=1-t;append([q*q*q*a[0]+3*q*q*t*b[0]+3*q*t*t*c[0]+t*t*t*d[0],q*q*q*a[1]+3*q*q*t*b[1]+3*q*t*t*c[1]+t*t*t*d[1]]);}}
  else if(command==='Z'){if(polygon&&polygon.length>1)polygon.push(polygon[0]);command='';}
  else throw Error('暂不支持此字的轮廓格式。');
 }
 return polygons;
}
export function glyphFromData(char,data){
 if(!Array.isArray(data?.medians)||data.medians.length!==data.strokes?.length)throw Error(`「${char}」缺少可用笔顺。`);
 return sculptAutomaticGlyph(char,data,data.strokes.map(outlinePolygons));
}
function bounds(glyph){const box=new T.Box3();for(const s of glyph.strokes)for(const p of s.a?[...s.a,...s.b]:s.points)box.expandByPoint(new T.Vector3(...p));return box;}
function transformStroke(s,kind,scale,offset,center){
 const move=([x,y,z])=>[(x-center.x)*scale+offset.x,(y-center.y)*scale+offset.y,z*scale];
 return kind==='centerline'?{...s,kind,points:s.points.map(move),width:s.width.map(n=>n*scale),thickness:s.thickness.map(n=>n*scale)}:{...s,kind,a:s.a.map(move),b:s.b.map(move)};
}
export async function createTextGlyph(value,{variantId='01',style='running',loader=loadCharacter}={}){
 const inputText=cleanText(value),chars=[...inputText],parts=[];
 for(const char of chars){
  const alias=char;
  let base=(style==='running'&&runningGlyphs.find(g=>g.text===char))||(style==='cursive'&&cursiveGlyphs.find(g=>g.text===char))||catalog.find(g=>g.text===alias&&(alias!=='楊'||g.id===variantId));
  if(!base){if(!derived.has(char))derived.set(char,glyphFromData(char,await loader(char)));base=derived.get(char);}
  parts.push(base);
 }
 const columns=Math.min(4,parts.length),rows=Math.ceil(parts.length/columns),strokes=[],legacyStrokes=[],referenceV8Strokes=[],referenceV9Strokes=[],referenceV10Strokes=[],charSources=[];let clock=.06;
 parts.forEach((base,index)=>{
  const row=Math.floor(index/columns),col=index%columns,rowCount=Math.min(columns,parts.length-row*columns),box=bounds(base),size=box.getSize(new T.Vector3()),center=box.getCenter(new T.Vector3());
  const scale=parts.length===1?1:3.18/Math.max(size.x,size.y),offset=new T.Vector3((col-(rowCount-1)/2)*3.46,((rows-1)/2-row)*3.65,0);
  // Single input keeps the established model placement exactly.
  if(parts.length===1){center.set(0,0,0);offset.set(0,0,0);}
  for(const [strokeIndex,s] of base.strokes.entries()){const next=transformStroke(s,base.kind,scale,offset,center);next.name=base.text+' · '+s.name.replace(new RegExp('^'+base.text+' · '),'');next.start=clock+s.start-base.writeStart;next.end=clock+s.end-base.writeStart;next.character=index;strokes.push(next);const prior=transformStroke(base.legacyStrokes?.[strokeIndex]||s,base.kind,scale,offset,center);legacyStrokes.push({...prior,name:next.name,start:next.start,end:next.end,character:index});const v8=transformStroke(base.referenceV8Strokes?.[strokeIndex]||s,base.kind,scale,offset,center);referenceV8Strokes.push({...v8,name:next.name,start:next.start,end:next.end,character:index});for(const [field,destination] of [['referenceV9Strokes',referenceV9Strokes],['referenceV10Strokes',referenceV10Strokes]]){const old=base[field]?.[strokeIndex]||s,prior=transformStroke(old,base.kind,scale,offset,center);destination.push({...prior,name:base.text+' · '+old.name,start:clock+old.start-base.writeStart,end:clock+old.end-base.writeStart,character:index});}}
  clock+=base.writeEnd-base.writeStart+.16;charSources.push({character:base.text,running:!!base.running,cursive:!!base.cursive,detailLevel:base.detailLevel||'sculpted',...base.source});
 });
 const writeEnd=strokes.at(-1).end,one=parts.length===1,text=parts.map(p=>p.text).join(''),source=one?parts[0].source:{name:text+' · 立体连写',phrase:'从左至右，依笔势逐字书写',url:charSources[0].url,image:'',caption:'各字依据见下方',description:'每个字保留独立的笔势与空间层次。原帖临写、单独设计与通用字形的依据逐字列在下方；其中楊沿用所选临写版本，琪采用本地设计的行书笔势。'};
 const running=charSources.filter(s=>s.running).length,cursive=charSources.filter(s=>s.cursive).length;
 const sculpted=charSources.filter(s=>s.detailLevel==='sculpted').length,automatic=parts.length-sculpted,modeling={sculpted,automatic,label:automatic?(sculpted?`逐笔设计 ${sculpted} 字 / 自动造型 ${automatic} 字`:'通用自动造型'):'逐笔设计'};
 if(!one)source.description=`本组 ${parts.length} 字中，逐笔设计 ${sculpted} 字，通用自动造型 ${automatic} 字。每个字保留独立的笔势与空间层次，依据逐字列在下方。自动造型不等同于人工精修。`;
 return {id:'text:'+text,generated:true,inputText,text,title:one?parts[0].title:'连写',subtitle:one?parts[0].subtitle:`${parts.length} 字 · ${strokes.length} 段笔势`,kind:'mixed',strokes,legacyStrokes,referenceV9Strokes:parts.some(p=>p.referenceV9Strokes)?referenceV9Strokes:undefined,referenceV10Strokes:parts.some(p=>p.referenceV10Strokes)?referenceV10Strokes:undefined,referenceV8Strokes:parts.some(p=>p.referenceV8Strokes)?referenceV8Strokes:undefined,writeStart:.06,writeEnd,frontalAt:one?parts[0].frontalAt:writeEnd+1.45,duration:one?parts[0].duration:Math.ceil(writeEnd+2.8),source,charSources,modeling:{...modeling,running,cursive},glyphStyle:style,components:parts.map(p=>p.id),requiresLicense:parts.some(p=>p.requiresLicense||p.kind==='centerline'||p.id.startsWith('data:'))};
}
