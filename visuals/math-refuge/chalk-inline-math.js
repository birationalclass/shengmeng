import {resourceFetch} from './resource-fetch.js';
// Simple inline radicals share measured geometry with their reveal bounds.
// Full formulas use the prebuilt MathJax SVGs.
import {authoredFormula} from './authored-chalk.js?v=inline-formula-2';
import {chalkInlineRuns} from './chalk-typography.js?v=inline-formula-2';
import {preparationTurn} from './preparation-turn.js';
let atlasJob;const images=new Map(),metrics=new Map();
export async function prepareInlineMath(text,mathStyle='mali-italic'){
 const atlas=await(atlasJob??=resourceFetch('./assets/chalk/inline-math/index.json').then(r=>{if(!r.ok)throw Error('行内公式索引未就绪');return r.json();}).catch(error=>{atlasJob=null;throw error;}));
 // Parse each outline once; colour variants share the measured stroke geometry.
 for(const run of new Set(chalkInlineRuns(text).filter(r=>r.math&&!r.radical).map(r=>r.text))){const m=atlas.runs[run];if(!m)continue;metrics.set(run,m);const baseKey=mathStyle+run+'#eee9d5';
  if(!images.has(baseKey)){const job=authoredFormula('./assets/chalk/inline-math/'+m.file,{mathStyle});images.set(baseKey,job);try{images.set(baseKey,await job);}catch(error){images.delete(baseKey);throw error;}}
  const base=await images.get(baseKey);
  for(const color of ['#93c9ff','#ffada3','#e4cf9c']){const key=mathStyle+run+color;if(images.has(key))continue;await preparationTurn();const c=document.createElement('canvas');c.width=base.naturalWidth||base.width;c.height=base.naturalHeight||base.height;const ctx=c.getContext('2d');ctx.drawImage(base,0,0);ctx.globalCompositeOperation='source-in';ctx.fillStyle=color;ctx.fillRect(0,0,c.width,c.height);c.authoredOperations=base.authoredOperations?.map(op=>({...op,chalkColor:color}));images.set(key,c);}
 }
}
export function inlineInk(ctx,run,size){
 const m=run.math&&!run.radical&&metrics.get(run.text);if(m){const k=size/m.em;return{width:m.width*k,actualBoundingBoxLeft:0,actualBoundingBoxRight:m.width*k,actualBoundingBoxAscent:m.ascent*k,actualBoundingBoxDescent:m.descent*k};}
 const ink=ctx.measureText(run.text);if(!run.radical)return ink;
 const width=size*.52+Math.max(ink.width,ink.actualBoundingBoxRight||0)+size*.12;
 const ascent=Math.max(size*.83,(ink.actualBoundingBoxAscent??size*.8)+size*.12);
 return {width,actualBoundingBoxLeft:0,actualBoundingBoxRight:width,actualBoundingBoxAscent:ascent+size*.026,actualBoundingBoxDescent:Math.max(ink.actualBoundingBoxDescent||0,size*.046)};
}
export function drawInlineInk(ctx,run,x,y,size){
 const m=run.math&&!run.radical&&metrics.get(run.text),image=m&&images.get((run.mathStyle||'mali-italic')+run.text+ctx.fillStyle);if(image&&!(image instanceof Promise)){const k=size/m.em;ctx.drawImage(image,x,y-m.ascent*k,m.width*k,m.height*k);return;}
 if(!run.radical){ctx.fillText(run.text,x,y);return;}
 const ink=inlineInk(ctx,run,size),top=y-ink.actualBoundingBoxAscent+size*.026;
 const points=[[x+size*.025,y-size*.28],[x+size*.14,y-size*.35],[x+size*.28,y+size*.02],[x+size*.49,top],[x+ink.width-size*.025,top]];
 const width=Math.max(1,size*.05),color=ctx.fillStyle;
 if(ctx.chalkStroke)ctx.chalkStroke(points,width,color);
 else{ctx.save();ctx.strokeStyle=color;ctx.lineWidth=width;ctx.lineCap='round';ctx.lineJoin='round';ctx.beginPath();points.forEach(([a,b],i)=>i?ctx.lineTo(a,b):ctx.moveTo(a,b));ctx.stroke();ctx.restore();}
 ctx.fillText(run.text,x+size*.52,y);
}
