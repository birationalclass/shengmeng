import {resourceFetch} from './resource-fetch.js';
import {decodeImage} from './mobile-runtime.js';
import {preparationTurn} from './preparation-turn.js';
import {chineseMetrics,paintGlyph} from './chinese-chalk.js?v=safari-glyph-20261019-1';

// Independent typography defaults. Math layout and structural symbols still
// belong to the formula layer; neither choice changes Chinese or screen UI.
export const ENGLISH_CHALK_STYLE='mali-italic';
export const MATH_CHALK_STYLE='mali-italic';
export const MALI_GLYPH_ASSET=new URL('./assets/chalk/mali-italic/latin-72817c18b9a4.json',import.meta.url);
const EXTENDED_ASSET=new URL('./assets/chalk/mali-italic/extended-de8ca4e1e292.json',import.meta.url);
let assetJob,extendedJob;const jobs=new Map(),ready=new Map();
const canvas=n=>{const c=document.createElement('canvas');c.width=c.height=n;return c;};
export function maliGlyph(char){return ready.get(char);}
export function maliMetrics(g,size){return chineseMetrics(g,size);}
export function fitMaliGlyph(g,box){
 const [left,top,right,bottom]=g.bounds,k=Math.min(box.width/(right-left),box.height/(bottom-top));
 return {scale:k,x:box.x+(box.width-(right-left)*k)/2-left*k,y:box.y+(box.height-(bottom-top)*k)/2-top*k};
}
async function decodeGlyph(data){
 const [image,timing]=await Promise.all([decodeImage(data.ink),decodeImage(data.timeMap)]),c=canvas(data.width),ctx=c.getContext('2d',{willReadFrequently:true});
 ctx.drawImage(image,0,0);const ink=ctx.getImageData(0,0,data.width,data.width).data;
 ctx.clearRect(0,0,data.width,data.width);ctx.drawImage(timing,0,0);const time=ctx.getImageData(0,0,data.width,data.width).data;
 const n=data.width*data.width,alpha=new Uint8Array(n),owner=new Uint8Array(n),phase=new Uint8Array(n),boxes=data.paths.map(()=>[data.width,data.width,-1,-1]);
 for(let i=0;i<n;i++){alpha[i]=ink[i*4+3];owner[i]=time[i*4];phase[i]=time[i*4+1];if(owner[i]){const x=i%data.width,y=Math.floor(i/data.width),b=boxes[owner[i]-1];b[0]=Math.min(b[0],x);b[1]=Math.min(b[1],y);b[2]=Math.max(b[2],x);b[3]=Math.max(b[3],y);}}
 const strokes=data.paths.map((points,i)=>{const [x,y,r,b]=boxes[i];return{index:i+1,points,box:[x,y,r-x+1,b-y+1]};});c.width=c.height=1;
 return {...data,image,alpha,owner,phase,strokes,colors:new Map(),urls:new Map([['#eee9d5',data.ink]])};
}
export async function prepareMaliChalk(text){
 const asset=await(assetJob??=resourceFetch(MALI_GLYPH_ASSET).then(r=>{if(!r.ok)throw Error('Mali 板书字形未就绪');return r.json();}).then(data=>new Map(data.glyphs.map(g=>[g.char,g]))).catch(e=>{assetJob=null;throw e;}));
 if([...String(text)].some(c=>c.codePointAt(0)>127&&/\p{Script=Latin}/u.test(c))){const extra=await(extendedJob??=resourceFetch(EXTENDED_ASSET).then(r=>{if(!r.ok)throw Error('Mali 扩展字形未就绪');return r.json();}).catch(e=>{extendedJob=null;throw e;}));for(const g of extra.glyphs)asset.set(g.char,g);}
 const chars=[...new Set([...String(text)].filter(c=>asset.has(c)))];let at=0;
 await Promise.all(Array.from({length:Math.min(4,chars.length)},async()=>{while(at<chars.length){const c=chars[at++];if(!jobs.has(c))jobs.set(c,decodeGlyph(asset.get(c)).catch(e=>{jobs.delete(c);throw e;}));ready.set(c,await jobs.get(c));await preparationTurn();}}));
 // Rows retain the few decoded glyphs that they need. Bound the shared lookup.
 for(const c of ready.keys())if(ready.size>128&&!chars.includes(c)){ready.delete(c);jobs.delete(c);}
}
export function maliOperations(g,x,y,size,color){
 const k=size/g.fontSize,[ox,oy]=g.origin,group={},glyphRect=[x-ox*k,y-oy*k,g.width*k,g.width*k];
 return g.strokes.map(s=>{const [a,b,w,h]=s.box,rect=[x+(a-ox)*k,y+(b-oy)*k,w*k,h*k];return{rect,strokePath:s.points.map(([a,b])=>[x+(a-ox)*k,y+(b-oy)*k]),strokeRaster:{stroke:s,rect,group,glyph:g,glyphRect},letterGroup:group,letterSeconds:(/[A-Z]/.test(g.char)?.32:/[a-z0-9]/.test(g.char)?.25:.16)/g.strokes.length,chalkColor:color,character:g.char};});
}
export function paintMali(ctx,g,x,y,size,color){const k=size/g.fontSize,[ox,oy]=g.origin;paintGlyph(ctx,g,[x-ox*k,y-oy*k,g.width*k,g.width*k],0,1,color,true);}
export function maliInkURL(g,color){if(!g.urls.has(color)){const c=canvas(g.width);paintGlyph(c.getContext('2d'),g,[0,0,g.width,g.width],0,1,color,true);g.urls.set(color,c.toDataURL());c.width=c.height=1;}return g.urls.get(color);}
