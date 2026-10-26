import {resourceFetch} from './resource-fetch.js';
import {decodeImage} from './mobile-runtime.js';
// Original Honglei 36 raster ink, with independently owned stroke masks.
// Load just the current page's glyphs. No font binary or runtime font fallback.
const BASE=new URL('./assets/chalk/chinese36/',import.meta.url);
export const CHINESE_STROKE_SECONDS=1/16;
const canvas=(w,h)=>{const c=document.createElement('canvas');c.width=w;c.height=h;return c;};
const colorRGB=color=>{const value=String(color),h=value.replace('#',''),rgb=value.match(/^rgba?\(\s*(\d+)\D+(\d+)\D+(\d+)/);return rgb?rgb.slice(1,4).map(Number):h.length===6?[0,2,4].map(i=>parseInt(h.slice(i,i+2),16)):[238,233,213];};
const groups=new WeakMap(),partialBuffers=new WeakMap();
export function paintGlyph(ctx,g,rect,index,progress,color,complete=false){
 const rgb=colorRGB(color),key=rgb.join(',');let image=complete?(key==='238,233,213'?g.image:g.colors.get(key)):null;
 if(!image){
  // Keep each glyph's mutable surface separate. Completed colored glyphs are
  // written from their pixels directly, never copied from a shared canvas that
  // can be changed before a browser's deferred canvas/GPU copy is consumed.
  let buffer=complete?null:partialBuffers.get(g);
  if(!buffer){const image=canvas(g.width,g.width),context=image.getContext('2d');buffer={image,context,data:context.createImageData(g.width,g.width)};if(!complete)partialBuffers.set(g,buffer);}
  const target=buffer.data.data,limit=Math.round(progress*255);
  for(let i=0;i<g.alpha.length;i++){const k=i*4;target[k]=rgb[0];target[k+1]=rgb[1];target[k+2]=rgb[2];target[k+3]=complete||g.owner[i]<index||g.owner[i]===index&&g.phase[i]<=limit?g.alpha[i]:0;}
  buffer.context.putImageData(buffer.data,0,0);image=buffer.image;
  if(complete)g.colors.set(key,image);
 }
 ctx.drawImage(image,...rect);
}
// Composite the current character once, at source resolution. Drawing cropped
// strokes separately after scaling would introduce pale anti-alias seams.
export function paintChineseGroup(ctx,rows,row,progressForRow){
 let lookup=groups.get(rows);if(!lookup){lookup=new Map();for(let i=0;i<rows.length;i++){const key=rows[i].strokeRaster?.group;if(key){if(!lookup.has(key))lookup.set(key,[]);lookup.get(key).push(i);}}groups.set(rows,lookup);}
 const op=rows[row],indices=lookup.get(op.strokeRaster.group);if(row!==indices[0])return;
 let index=0,progress=0,complete=true;for(const i of indices){const p=progressForRow(i);if(p<=0){complete=false;break;}index=rows[i].strokeRaster.stroke.index;progress=p;if(p<1){complete=false;break;}}
 if(!index)return;paintGlyph(ctx,op.strokeRaster.glyph,op.strokeRaster.glyphRect,index,progress,op.chalkColor,complete);
}
export function chineseMetrics(g,size){const k=size/g.fontSize,[x,y,r,b]=g.bounds,[ox,oy]=g.origin;return{width:g.advance*k,actualBoundingBoxLeft:(ox-x)*k,actualBoundingBoxRight:(r-ox)*k,actualBoundingBoxAscent:(oy-y)*k,actualBoundingBoxDescent:(b-oy)*k};}
async function loadGlyph(meta){
 const data=await resourceFetch(new URL(meta.data,BASE)).then(r=>{if(!r.ok)throw Error('中文笔画资产加载失败：'+meta.char);return r.json();});
 const [im,timing]=await Promise.all([decodeImage(new URL(data.ink,BASE)),decodeImage(new URL(data.timeMap,BASE))]);
 const full=canvas(data.width,data.width),map=canvas(data.width,data.width);full.getContext('2d').drawImage(im,0,0);map.getContext('2d').drawImage(timing,0,0);
 const ink=full.getContext('2d').getImageData(0,0,data.width,data.width).data,time=map.getContext('2d').getImageData(0,0,data.width,data.width).data,strokes=[];
 const boxes=data.paths.map(()=>[data.width,data.width,-1,-1]);
 for(let i=0;i<time.length;i+=4)if(time[i]){const p=i/4,x=p%data.width,y=Math.floor(p/data.width),b=boxes[time[i]-1];b[0]=Math.min(b[0],x);b[1]=Math.min(b[1],y);b[2]=Math.max(b[2],x);b[3]=Math.max(b[3],y);}
 for(let index=1;index<=data.paths.length;index++)if(data.pixelCounts[index-1]){const [left,top,right,bottom]=boxes[index-1];strokes.push({index,points:data.paths[index-1],box:[left,top,right-left+1,bottom-top+1]});}
 const alpha=new Uint8Array(data.width*data.width),owner=new Uint8Array(alpha.length),phase=new Uint8Array(alpha.length);for(let i=0;i<alpha.length;i++){alpha[i]=ink[i*4+3];owner[i]=time[i*4];phase[i]=time[i*4+1];}
 full.width=map.width=1;return {...meta,image:im,strokes,alpha,owner,phase,colors:new Map()};
}
export async function createChineseChalk(){
 const index=await resourceFetch(new URL('index.json?v=course-ready-glyphs-20261026',BASE)).then(r=>{if(!r.ok)throw Error('中文板书字形索引未就绪');return r.json();}),metadata=new Map(index.glyphs.map(g=>[g.char,g])),jobs=new Map();
 async function prepare(text){
  const chars=[...new Set([...String(text)].filter(c=>/[\u3400-\u9fff，。；：（）！？、…·]/.test(c)))];
  for(const c of chars)if(!metadata.has(c))throw Error('36号板书字形缺失：'+c);
  const entries=[];let cursor=0,failed=false;
  await Promise.all(Array.from({length:Math.min(4,chars.length)},async()=>{while(cursor<chars.length&&!failed){const c=chars[cursor++];try{if(!jobs.has(c))jobs.set(c,loadGlyph(metadata.get(c)).catch(e=>{jobs.delete(c);throw e;}));entries.push(await jobs.get(c));}catch(error){failed=true;throw error;}}}));
  const ready=new Map(entries.map(g=>[g.char,g]));
  for(const c of jobs.keys())if(jobs.size>160&&!ready.has(c))jobs.delete(c);
  return {glyph:c=>ready.get(c),measure:(g,size)=>chineseMetrics(g,size),
   operations(g,x,y,size,color){const k=size/g.fontSize,[ox,oy]=g.origin,group=g.char+':'+x+':'+y+':'+size,glyphRect=[x-ox*k,y-oy*k,g.width*k,g.width*k];return g.strokes.map(s=>{const [a,b,w,h]=s.box,rect=[x+(a-ox)*k,y+(b-oy)*k,w*k,h*k];return {rect,strokePath:s.points.map(([a,b])=>[x+(a-ox)*k,y+(b-oy)*k]),strokeRaster:{stroke:s,rect,group,glyph:g,glyphRect},strokeSeconds:CHINESE_STROKE_SECONDS,chalkColor:color,character:g.char};});},
   paint(ctx,g,x,y,size,color){const k=size/g.fontSize,[ox,oy]=g.origin;paintGlyph(ctx,g,[x-ox*k,y-oy*k,g.width*k,g.width*k],0,1,color,true);}
  };
 }
 return {index,metadata,prepare};
}
