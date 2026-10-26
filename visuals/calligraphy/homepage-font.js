import {homepageCharacters} from './homepage-coverage.js';
import {paintHomepageGlyph,meshFromAlpha} from './font-volume.js?v=20';
import {textPlacements} from './text-layout.js';

const bundles=new Map(),meshes=new Map();
export async function loadHomepageCharacter(char){
 if(!homepageCharacters.has(char))throw Error('主页原字库没有「'+char+'」，请在设置中选择简体或保留原文。');
 const key=(char.codePointAt(0)>>8).toString(16);
 if(!bundles.has(key))bundles.set(key,fetch('assets/homepage/glyphs/'+key+'.json').then(r=>{if(!r.ok)throw Error('主页字体未能载入。');return r.json();}).catch(e=>{bundles.delete(key);throw e;}));
 return (await bundles.get(key))[char];
}
function rasterize(g,n){const canvas=document.createElement('canvas');canvas.width=n;canvas.height=n;const ctx=canvas.getContext('2d',{willReadFrequently:true});paintHomepageGlyph(ctx,g,n);const bytes=ctx.getImageData(0,0,n,n).data;return Uint8Array.from({length:n*n},(_,i)=>bytes[i*4+3]);}
export async function createHomepageText(text,{layout='auto',loader,rasterizer=rasterize,resolution=260,fontLoader=loadHomepageCharacter}={}){
 const chars=[...text],placement=textPlacements(chars.length,layout),strokes=[],charSources=[],flatGlyphs=[];let time=.06;
 for(const [i,char] of chars.entries()){
  const font=await fontLoader(char),key=char+':'+resolution;
  if(!meshes.has(key)){let medians=[];try{medians=(await loader(char)).medians;}catch{}meshes.set(key,meshFromAlpha(await rasterizer(font,resolution),resolution,medians));}
  const mesh=meshes.get(key),duration=Math.max(.58,Math.min(1.35,.28+mesh.strokeCount*.095)),offset=placement[i];
  strokes.push({name:char+' · 主页行书',kind:'font-volume',mesh,offset,start:time,end:time+duration,motion:[0,1]});time+=duration+.08;
  flatGlyphs.push({character:char,font,offset});
  charSources.push({character:char,homepage:true,detailLevel:'font-volume',name:'主页行书 · '+char,phrase:font.titleOriginal?'与主页标题相同的原始字形':'同一 Zhi Mang Xing 字族',url:'https://birationalclass.github.io/shengmeng/',image:'',caption:'原字体轮廓',description:'保留主页字体、加粗轮廓、倾斜与等宽字格；圆润体积、空间起伏和动画为本项目重建。原字体未记录真实笔顺，表面生长节奏依可用笔顺估计。'});
 }
 const writeEnd=strokes.at(-1).end;
 return {id:'homepage:'+text,text,inputText:text,title:'主页行书',subtitle:layout==='homepage'?'右起双列 · 天之道 / 损有余而补不足':'主页原字形 · 圆润立体笔面',generated:true,homepage:true,glyphStyle:'homepage',layout,kind:'font-volume',strokes,flatGlyphs,charSources,modeling:{homepage:chars.length,sculpted:0,automatic:0,label:'主页原字形 · 立体曲面'},writeStart:.06,writeEnd,frontalAt:writeEnd+1.45,duration:Math.ceil(writeEnd+2.65),source:{name:'主页「天之道」同款字势',phrase:layout==='homepage'?'右列三字，左列七字；左列下错 0.43 字格':'Zhi Mang Xing · 原字形曲面化',url:'https://birationalclass.github.io/shengmeng/',image:'assets/homepage/prototype.png',caption:'主页原字形与双列布局',description:'使用主页十字的原始标题轮廓，其余字来自同一字族。等宽字格、1.14 字格列距和 0.43 字格错位来自主页。轮廓围成闭合的圆润立体曲面，厚度随笔画宽度变化；运笔时序为本地重建。'},requiresHomepageLicense:true};
}
export function flatHomepagePaths(glyph){
 const k=3.18/1024,skew=-Math.tan(5*Math.PI/180)*1.08,paths=[];let minX=Infinity,minY=Infinity,maxX=-Infinity,maxY=-Infinity;
 for(const {font:g,offset} of glyph.flatGlyphs){
  const r=820/g.units,a=1.08*r*k,b=0,c=-skew*r*k,d=-1.08*r*k,e=(512+1.08*(-g.advance*r/2)+skew*(520-512)-512)*k+offset.x,f=(512+1.08*(520-512)-512)*k-offset.y;
  const matrix=[a,b,c,d,e,f];paths.push({d:g.path,transform:'matrix('+matrix.join(' ')+')',stroke:18/r,character:g.character});
  for(const x of [g.bounds[0],g.bounds[2]])for(const y of [g.bounds[1],g.bounds[3]]){const px=a*x+c*y+e,py=b*x+d*y+f;minX=Math.min(minX,px-.06);maxX=Math.max(maxX,px+.06);minY=Math.min(minY,py-.06);maxY=Math.max(maxY,py+.06);}
 }const pad=.12;return {paths,viewBox:[minX-pad,minY-pad,maxX-minX+pad*2,maxY-minY+pad*2]};
}
