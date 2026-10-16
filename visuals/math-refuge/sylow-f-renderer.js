import {prepareMaliChalk} from './mali-chalk.js';
import {createChineseChalk,paintChineseGroup} from './chinese-chalk.js';
import {authoredContext,authoredFormula} from './authored-chalk.js';
import {writingPlan,inkGuides,strokeReveal,rasterStrokeReveal,inkReveal,erasingPlan} from './chalk-motion.js';
import {paintChalkStroke} from './chalk-annotations.js';
import {drawReferenceIcon} from './classroom-metadata.js';
const COLORS={white:'#eee9d5',gold:'#e4cf9c',blue:'#93c9ff',caution:'#ffada3'};
let libraryPromise;const formulas=new Map();
async function formula(token,color='#eee9d5'){const key=token.asset+color;if(!formulas.has(key))formulas.set(key,authoredFormula(token.asset,{color}));return formulas.get(key);}
const glyphText=b=>b.rows.map(r=>r.display.replace(/\$[^$]+\$/g,'')).join('');
function appendStroke(ctx,points,color,width=2.1){ctx.chalkStroke(points,width,color);}
function object(ctx,o){
 if(o.type==='label'){ctx.fillStyle=o.color;ctx.font='28px RefugeLatin, RefugeChinese';ctx.fillText(o.text,o.x,o.y);return;}
 const pts=o.points;if(o.dashed){for(let k=1;k<pts.length;k++){const [x,y]=pts[k-1],[u,v]=pts[k],n=Math.ceil(Math.hypot(u-x,v-y)/13);for(let i=0;i<n;i+=2)appendStroke(ctx,[[x+(u-x)*i/n,y+(v-y)*i/n],[x+(u-x)*Math.min(i+1,n)/n,y+(v-y)*Math.min(i+1,n)/n]],o.color,1.8);}}
 else appendStroke(ctx,pts,o.color);
 if(o.arrow){const [x,y]=pts.at(-1),[u,v]=pts.at(-2),ang=Math.atan2(y-v,x-u);appendStroke(ctx,[[x-10*Math.cos(ang-.45),y-10*Math.sin(ang-.45)],[x,y],[x-10*Math.cos(ang+.45),y-10*Math.sin(ang+.45)]],o.color);}
}
export async function prepareBoard(b,language='zh'){
 const source=b;if(b.kind==='break')b={...b,kind:'cover',rows:[{display:'课间休息',en:'Break',tokens:[{text:'课间休息'}],enTokens:[{text:'Break'}],color:'gold'}]};
 libraryPromise??=createChineseChalk();const library=await libraryPromise;
 await prepareMaliChalk(b.rows.map(r=>r.display+' '+r.en).join(''));
 const chinese=await library.prepare(glyphText(b)),canvas=document.createElement('canvas');canvas.width=1536;canvas.height=640;
 const ctx=canvas.getContext('2d'),rec=authoredContext(ctx,chinese),cx=rec.ctx,original=[],sizes=[];
 let diagram=b.diagramAsset?await fetch(b.diagramAsset).then(r=>{if(!r.ok)throw Error(r.status);return r.json()}):null;
 const tokens=b.rows.map(r=>language==='en'?r.enTokens:r.tokens);
 await Promise.all(tokens.flat().filter(t=>t.asset).map(formula));
 for(let i=0;i<b.rows.length;i++){
  const r=b.rows[i],ts=tokens[i],pure=ts.length===1&&!!ts[0].asset;
  let size=b.kind==='cover'?(i===0?76:42):i===0?42:38;
  const limit=b.kind==='cover'?1360:i===0?1305:diagram?865:b.kind==='exercise'?1000:1328;
  function metrics(s){cx.font=`${s}px RefugeLatin, RefugeChinese`;return ts.map(t=>{if(t.asset){const vb=t.viewBox,k=s/1000;return {w:vb[2]*k,h:vb[3]*k,base:-vb[1]*k,img:true,t};}const m=cx.measureText(t.text);return {w:m.width,h:s,base:s*.8,t};});}
  let ms=metrics(size),w=ms.reduce((n,m)=>n+m.w,0);while((w>limit||Math.max(...ms.map(m=>m.h))>78)&&size>28){size--;ms=metrics(size);w=ms.reduce((n,m)=>n+m.w,0);}
  if(w>limit+1)throw Error(`Board line needs reflow: ${b.id}/${i}: ${w.toFixed(1)} > ${limit}`);
  sizes.push(size);let x=b.kind==='cover'?(1536-w)/2:i===0?136:pure?(diagram?88+(865-w)/2:(1536-w)/2):88;
  const y=b.kind==='cover'?[190,320,410,520][i]:i===0?76:158+(i-1)*83;
  const x0=x;cx.fillStyle=COLORS[r.color];cx.font=`${size}px RefugeLatin, RefugeChinese`;
  if(i===0&&b.kind!=='cover')drawReferenceIcon(cx,b.kind==='exercise'?'exercise':b.reference?.kind||'extension',84,38,36);
  for(const m of ms){if(m.img){const im=await formula(m.t,COLORS[r.color]);cx.drawImage(im,x,y-m.base,m.w,m.h);}else cx.fillText(m.t.text,x,y);x+=m.w;}
  original.push(Object.assign([i===0&&b.kind!=='cover'?80:x0-5,i===0&&b.kind!=='cover'?32:y-Math.max(...ms.map(m=>m.base))-6,w+10+(i===0&&b.kind!=='cover'?56:0),i===0&&b.kind!=='cover'?60:Math.max(size,...ms.map(m=>m.h))+14],{mainLine:i}));
 }
 const mainRows=rec.rows(original),stageRows=[];if(diagram)for(const [i,s]of diagram.stages.entries()){
  const stage=authoredContext(ctx,chinese);for(const id of s.objects)object(stage.ctx,diagram.objects.find(o=>o.id===id));
  stageRows.push(...stage.rows([Object.assign([...diagram.region],{mainLine:b.rows.length+i,auxiliaryDiagram:true})]));
 }
 const rows=diagram?[...mainRows.filter(r=>r.mainLine<=b.diagramAfterRow),...stageRows,...mainRows.filter(r=>r.mainLine>b.diagramAfterRow)]:mainRows;
 const guides=inkGuides(ctx.getImageData(0,0,1536,640),rows),plan=writingPlan(rows,guides);
 const logical={};for(const s of plan.segments){const k=rows[s.row].mainLine;(logical[k]??={cost:0,startCost:Infinity,endCost:0}).cost+=s.cost;}
 let accumulated=0;for(const s of plan.segments){const q=logical[rows[s.row].mainLine];q.startCost=Math.min(q.startCost,accumulated);accumulated+=s.cost;q.endCost=accumulated;}
 for(const q of Object.values(logical))q.seconds=q.cost/plan.total*plan.duration;
 const erase=erasingPlan(ctx.getImageData(0,0,1536,640),rows);
 return {b:source,canvas,rows,guides,plan,logical,sizes,diagram,eraseSeconds:erase.duration};
}
export function paintPrepared(ctx,a,fractions={},metadata=true){
 ctx.fillStyle='#06271c';ctx.fillRect(0,0,1536,640);
 const pose=(row)=>{const q=a.logical[a.rows[row].mainLine],f=fractions[a.rows[row].mainLine]||0;return(q.startCost+q.cost*f)/a.plan.total;};
 for(let i=0;i<a.rows.length;i++){
  const r=a.rows[i],f=fractions[r.mainLine]||0;if(f<=0)continue;const p=pose(i);
  if(r.strokeRaster)paintChineseGroup(ctx,a.rows,i,j=>{const rr=a.rows[j];if(rr.mainLine!==r.mainLine)return 0;return rasterStrokeReveal(a.rows,p,j,a.guides)});
  else if(r.strokePath)paintChalkStroke(ctx,strokeReveal(a.rows,p,i,a.guides),r.chalkColor,r.strokeWidth);
  else {const w=inkReveal(a.rows,p,i,a.guides);if(w>0){ctx.save();ctx.beginPath();ctx.rect(r[0],r[1],w,r[3]);ctx.clip();ctx.drawImage(a.canvas,0,0);ctx.restore();}}
 }
 if(metadata&&a.b.kind!=='break'){
  ctx.fillStyle='rgba(228,207,156,.1)';ctx.font='54px RefugeLatin';ctx.textAlign='left';ctx.textBaseline='alphabetic';
  const top=ctx.measureText('§2.6');ctx.fillText('§2.6',1504-top.actualBoundingBoxRight,32+top.actualBoundingBoxAscent);
  const s=`${a.b.page+1} / ${a.total||'—'}`,m=ctx.measureText(s);ctx.fillText(s,1504-m.actualBoundingBoxRight,608-(m.actualBoundingBoxDescent||0));
 }
}
