import {resourceFetch} from './resource-fetch.js';
import {decodeImage} from './mobile-runtime.js';
import {preparationTurn} from './preparation-turn.js';
import {glyphs,advance} from './refined-handwriting.js?v1';
import {maliGlyph,maliMetrics,maliOperations,paintMali,prepareMaliChalk,fitMaliGlyph,maliInkURL} from './mali-chalk.js?v=mali-20261017';
const NS='http://www.w3.org/2000/svg',samples=new Map();
export function authoredGlyph(char){
 if(samples.has(char))return samples.get(char);if(!glyphs[char]||typeof document.createElementNS!=='function')return null;
 const paths=glyphs[char].map(d=>{const p=document.createElementNS(NS,'path');p.setAttribute('d',d);const n=Math.max(3,Math.ceil(p.getTotalLength()/2)),points=[];for(let i=0;i<=n;i++){const a=p.getPointAtLength(p.getTotalLength()*i/n);points.push([a.x,a.y]);}return points;});
 const result={paths,box:pointBox(paths.flat()),advance:advance[char]||60};samples.set(char,result);return result;
}
export function pointBox(points,pad=0){const xs=points.map(p=>p[0]),ys=points.map(p=>p[1]);return [Math.min(...xs)-pad,Math.min(...ys)-pad,Math.max(...xs)-Math.min(...xs)+2*pad,Math.max(...ys)-Math.min(...ys)+2*pad];}
// Fit the painted glyph, including round caps, rather than its centre-line.
// A period has only a 1x1 centre-line: fitting that alone magnifies its pen width.
export const FORMULA_PEN_WIDTH=2.8;
export function formulaGlyphBox(glyph){const [x,y,w,h]=glyph.box,pad=FORMULA_PEN_WIDTH/2;return [x-pad,y-pad,w+2*pad,h+2*pad];}
export function clipRect(a,b){const x=Math.max(a[0],b[0]),y=Math.max(a[1],b[1]),r=Math.min(a[0]+a[2],b[0]+b[2]),bottom=Math.min(a[1]+a[3],b[1]+b[3]);return r>x&&bottom>y?[x,y,r-x,bottom-y]:null;}
export function clipPolyline(points,rect){const out=[];let current=[];for(let i=1;i<points.length;i++){const a=points[i-1],b=points[i],dx=b[0]-a[0],dy=b[1]-a[1],p=[-dx,dx,-dy,dy],q=[a[0]-rect[0],rect[0]+rect[2]-a[0],a[1]-rect[1],rect[1]+rect[3]-a[1]];let lo=0,hi=1,valid=true;for(let j=0;j<4;j++){if(p[j]===0){if(q[j]<0)valid=false;}else{const t=q[j]/p[j];if(p[j]<0)lo=Math.max(lo,t);else hi=Math.min(hi,t);}}if(!valid||lo>hi){if(current.length)out.push(current);current=[];continue;}const start=[a[0]+lo*dx,a[1]+lo*dy],end=[a[0]+hi*dx,a[1]+hi*dy];if(current.length&&Math.hypot(current.at(-1)[0]-start[0],current.at(-1)[1]-start[1])>.01){out.push(current);current=[];}if(!current.length)current.push(start);current.push(end);if(hi<1){out.push(current);current=[];}}if(current.length)out.push(current);return out;}
function stroke(ctx,points,width,color){ctx.save();ctx.strokeStyle=color;ctx.lineWidth=width;ctx.lineCap='round';ctx.lineJoin='round';ctx.beginPath();points.forEach(([x,y],i)=>i?ctx.lineTo(x,y):ctx.moveTo(x,y));ctx.stroke();ctx.restore();}
// A recording context lets the existing layout engine measure the new glyphs.
// Unsupported characters retain their native metrics and exact original ink.
export function authoredContext(ctx,chinese=null,{latin=true,latinStyle='mali-italic',mathStyle='mali-italic'}={}){
 const operations=[];const useMali=()=> (ctx.font.includes('RefugeMath')?mathStyle:latinStyle)==='mali-italic';const size=()=>Number(ctx.font.match(/([\d.]+)px/)?.[1]||40),scale=()=>size()/90;
 function measure(text){let width=0,left=0,right=0,ascent=0,descent=0;for(const char of String(text)){const cg=chinese?.glyph(char),mg=cg||!latin||!useMali()?null:maliGlyph(char),g=cg||mg||!latin||useMali()?null:authoredGlyph(char),k=scale(),m=cg?chinese.measure(cg,size()):mg?maliMetrics(mg,size()):g?{width:g.advance*k,actualBoundingBoxLeft:-g.box[0]*k,actualBoundingBoxRight:(g.box[0]+g.box[2])*k,actualBoundingBoxAscent:(72-g.box[1])*k,actualBoundingBoxDescent:(g.box[1]+g.box[3]-72)*k}:ctx.measureText(char);left=Math.max(left,(m.actualBoundingBoxLeft||0)-width);right=Math.max(right,width+(m.actualBoundingBoxRight??m.width));ascent=Math.max(ascent,m.actualBoundingBoxAscent||size()*.8);descent=Math.max(descent,m.actualBoundingBoxDescent||0);width+=m.width;}return {width,actualBoundingBoxLeft:left,actualBoundingBoxRight:right,actualBoundingBoxAscent:ascent,actualBoundingBoxDescent:descent};}
 function text(value,x,y){for(const char of String(value)){const cg=chinese?.glyph(char),mg=cg||!latin||!useMali()?null:maliGlyph(char),g=cg||mg||!latin||useMali()?null:authoredGlyph(char),k=scale(),color=ctx.fillStyle;if(cg){chinese.paint(ctx,cg,x,y,size(),color);operations.push(...chinese.operations(cg,x,y,size(),color));x+=chinese.measure(cg,size()).width;}else if(mg){paintMali(ctx,mg,x,y,size(),color);operations.push(...maliOperations(mg,x,y,size(),color));x+=maliMetrics(mg,size()).width;}else if(g){const width=Math.max(1.35,size()*.046),letterGroup={};for(const path of g.paths){const points=path.map(([a,b])=>[x+a*k,y+(b-72)*k]);stroke(ctx,points,width,color);operations.push({rect:pointBox(points,width/2+1),strokePath:points,strokeWidth:width,chalkColor:color,character:char,letterGroup,letterSeconds:(/[A-Z]/.test(char)?.32:/[a-z0-9]/.test(char)?.25:.16)/g.paths.length});}x+=g.advance*k;}else{const m=ctx.measureText(char);ctx.fillText(char,x,y);if(char.trim())operations.push({rect:[x-(m.actualBoundingBoxLeft||0)-1,y-(m.actualBoundingBoxAscent||size()*.8)-1,(m.actualBoundingBoxLeft||0)+(m.actualBoundingBoxRight??m.width)+2,(m.actualBoundingBoxAscent||size()*.8)+(m.actualBoundingBoxDescent||0)+2],chineseSpans:/[\u3400-\u9fff]/.test(char)?[[x,x+m.width]]:[]});x+=m.width;}}}
 function draw(image,...args){ctx.drawImage(image,...args);if(!image.authoredOperations)return;let sx=0,sy=0,sw=image.naturalWidth||image.width,sh=image.naturalHeight||image.height,dx,dy,dw,dh;if(args.length===8)[sx,sy,sw,sh,dx,dy,dw,dh]=args;else if(args.length===4)[dx,dy,dw,dh]=args;else{[dx,dy]=args;dw=sw;dh=sh;}const kx=dw/sw,ky=dh/sh,groups=new Map();for(const op of image.authoredOperations){const clipped=clipRect(op.rect,[sx,sy,sw,sh]);if(!clipped)continue;const [x,y,w,h]=clipped;const mapped={...op,rect:[dx+(x-sx)*kx,dy+(y-sy)*ky,w*kx,h*ky]};if(op.strokeRaster){const r=op.strokeRaster.glyphRect,key=op.strokeRaster.group;if(!groups.has(key))groups.set(key,{});mapped.strokeRaster={...op.strokeRaster,rect:mapped.rect,group:groups.get(key),glyphRect:[dx+(r[0]-sx)*kx,dy+(r[1]-sy)*ky,r[2]*kx,r[3]*ky]};mapped.letterGroup=groups.get(key);mapped.strokePath=op.strokePath?.map(([a,b])=>[dx+(a-sx)*kx,dy+(b-sy)*ky]);operations.push(mapped);continue;}if(op.symbolRect){const r=clipRect(op.symbolRect,[sx,sy,sw,sh]);mapped.symbolRect=r?[dx+(r[0]-sx)*kx,dy+(r[1]-sy)*ky,r[2]*kx,r[3]*ky]:null;}if(op.strokePath){const parts=clipPolyline(op.strokePath,[sx,sy,sw,sh]);for(const part of parts){const points=part.map(([a,b])=>[dx+(a-sx)*kx,dy+(b-sy)*ky]);operations.push({...mapped,rect:pointBox(points),strokePath:points,strokeWidth:op.strokeWidth*Math.sqrt(kx*ky)});}continue;}operations.push(mapped);}}
 const proxy=new Proxy(ctx,{get(target,key){if(key==='chalkStroke')return (points,width,color)=>{stroke(ctx,points,width,color);operations.push({rect:pointBox(points,width/2+1),strokePath:points,strokeWidth:width,chalkColor:color});};if(key==='measureText')return measure;if(key==='fillText')return text;if(key==='drawImage')return draw;const value=target[key];return typeof value==='function'?value.bind(target):value;},set(target,key,value){target[key]=value;return true;}});
 return {ctx:proxy,rows(original){const used=new Set();return original.flatMap(row=>{if(row.strokePath)return[row];const [x,y,w,h]=row;const inside=operations.filter((op,i)=>{if(used.has(i))return false;const [a,b,c,d]=op.rect,cx=a+c/2,cy=b+d/2;if(cx>=x-2&&cx<=x+w+2&&cy>=y-2&&cy<=y+h+2){used.add(i);return true;}return false;});return inside.length?inside.map(op=>Object.assign([...op.rect],op,{mainLine:row.mainLine,formulaRow:row.formulaRow,prose:row.prose,proofReason:row.proofReason,auxiliaryDiagram:row.auxiliaryDiagram})): [row];});}};
}

export async function authoredFormula(url,{color,mathStyle='mali-italic'}={}){
 const response=await resourceFetch(url);if(!response.ok)throw Error('板书公式加载失败');let source=await response.text();if(color)source=source.replaceAll('#eee9d5',color);
 const root=new DOMParser().parseFromString(source,'image/svg+xml').documentElement;
 if(root.localName!=='svg')throw Error('无效板书公式');
 if(mathStyle==='mali-italic')await prepareMaliChalk([...root.querySelectorAll('[data-c]')].map(e=>String.fromCodePoint(parseInt(e.getAttribute('data-c'),16)).normalize('NFKD')).join(''));
 const host=document.createElement('div');host.style.cssText='position:fixed;left:-20000px;top:0;visibility:hidden;pointer-events:none';host.append(root);document.body.append(host);const operations=[],rootMatrix=root.getScreenCTM().inverse();
 try{
 let batch=0;for(const element of [...root.querySelectorAll('path,rect,text,line,polyline,polygon,circle,ellipse')]){
  if(++batch%12===0)await preparationTurn();
  if(element.closest('defs')||!element.getBBox)continue;const box=element.getBBox(),m=rootMatrix.multiply(element.getScreenCTM());if(!m||!box.width&&!box.height)continue;
  const map=([x,y])=>[m.a*x+m.c*y+m.e,m.b*x+m.d*y+m.f];
  let clip=[0,0,Number(root.getAttribute('width')),Number(root.getAttribute('height'))];for(let parent=element.parentElement;parent&&parent!==root;parent=parent.parentElement){if(parent.localName==='svg'){const b=parent.getBoundingClientRect(),a=new DOMPoint(b.left,b.top).matrixTransform(rootMatrix),z=new DOMPoint(b.right,b.bottom).matrixTransform(rootMatrix);clip=clipRect(clip,[a.x,a.y,z.x-a.x,z.y-a.y]);if(!clip)break;}}if(!clip)continue;
  const symbolCode=parseInt(element.getAttribute('data-c')||'',16),symbol=Number.isFinite(symbolCode)?String.fromCodePoint(symbolCode).normalize('NFKD'):null;let topLevel=true;for(let p=element.parentElement;p&&p.getAttribute('data-mml-node')!=='math';p=p.parentElement){if(/^(mfrac|msub|msup|msubsup|munder|mover|munderover|msqrt|mroot)$/.test(p.getAttribute('data-mml-node')||''))topLevel=false;}const symbolRect=clipRect(pointBox([[box.x,box.y],[box.x+box.width,box.y],[box.x,box.y+box.height],[box.x+box.width,box.y+box.height]].map(map)),clip);
  const inkColor=getComputedStyle(element).fill||'#eee9d5',semantic={symbol,topLevel,symbolRect,chalkColor:inkColor};
  const record=(points,width)=>{for(const part of clipPolyline(points,clip))operations.push({...semantic,rect:clipRect(pointBox(part,width/2+1),clip),strokePath:part,strokeWidth:width,chalkColor:inkColor});};
  const code=parseInt(element.getAttribute('data-c')||'',16),char=Number.isFinite(code)?String.fromCodePoint(code).normalize('NFKD'):null;
  const compatible=code<128||(code>=0x1d434&&code<=0x1d467)||[0x210e,0x2212,0x2264,0x2265,0x21d2,0x21d4].includes(code);
  const mg=mathStyle==='mali-italic'&&compatible&&char&&/^[A-Za-z0-9.,:;!?]$/.test(char)?maliGlyph(char):null;
  const glyph=mathStyle==='refined'&&compatible&&char?authoredGlyph(char):null;
  const fraction=element.localName==='rect'&&element.parentElement?.getAttribute('data-mml-node')==='mfrac';
  if(['|','∣'].includes(symbol)&&box.height>box.width*4){
   // Write cardinality/absolute-value bars from top to bottom as one contact.
   // Their narrow filled outlines otherwise have no reliable scan columns.
   const local=[[box.x+box.width*.5,box.y+box.height],[box.x+box.width*.54,box.y+box.height*.5],[box.x+box.width*.5,box.y]],width=box.width*.86;
   record(local.map(map),Math.max(.8,width*Math.hypot(m.a,m.b)));
   const path=document.createElementNS(NS,'path');path.setAttribute('d',local.map(([x,y],i)=>(i?'L':'M')+x+' '+y).join(' '));path.setAttribute('fill','none');path.setAttribute('stroke',inkColor);path.setAttribute('stroke-width',String(width));path.setAttribute('stroke-linecap','round');if(element.hasAttribute('transform'))path.setAttribute('transform',element.getAttribute('transform'));element.replaceWith(path);
  }else if(mg&&box.width&&box.height){
   // Uniform fit: retain Mali's original aspect, existing MathJax baselines,
   // script placement and spacing. Never stretch letters into a math outline.
   const fit=fitMaliGlyph(mg,box),k=fit.scale,tx=fit.x,ty=2*box.y+box.height-fit.y;
   const image=document.createElementNS(NS,'image');image.setAttribute('href',maliInkURL(mg,inkColor));image.setAttribute('width',mg.width);image.setAttribute('height',mg.width);image.setAttribute('transform',`matrix(${k} 0 0 ${-k} ${tx} ${ty})`);
   const group=document.createElementNS(NS,'g');if(element.hasAttribute('transform'))group.setAttribute('transform',element.getAttribute('transform'));group.append(image);element.replaceWith(group);
   const points=p=>map([tx+p[0]*k,ty-p[1]*k]),glyphRect=pointBox([[0,0],[mg.width,mg.width]].map(points)),id={};
   for(const s of mg.strokes){const [x,y,w,h]=s.box,rect=clipRect(pointBox([[x,y],[x+w,y+h]].map(points)),clip);if(!rect)continue;operations.push({...semantic,rect,strokePath:s.points.map(points),strokeRaster:{stroke:s,rect,group:id,glyph:mg,glyphRect},letterGroup:id,letterSeconds:(/[A-Z]/.test(char)?.32:/[a-z0-9]/.test(char)?.25:.16)/mg.strokes.length,character:char});}
  }else if(glyph&&box.width&&box.height){
   // Words inside a formula (e.g. "even" and "odd") are still handwriting,
   // rather than mathematical symbols whose tiny bounds set their speed.
   if(/^[A-Za-z]$/.test(char)&&element.closest('[data-mml-node="mtext"]'))Object.assign(semantic,{character:char,letterGroup:{},letterSeconds:(/[A-Z]/.test(char)?.32:.25)/glyph.paths.length});
   const [gx,gy,gw,gh]=formulaGlyphBox(glyph),sx=box.width/gw,sy=box.height/gh;
   const group=document.createElementNS(NS,'g');if(element.hasAttribute('transform'))group.setAttribute('transform',element.getAttribute('transform'));
   for(let i=0;i<glyph.paths.length;i++){
    const points=glyph.paths[i].map(([x,y])=>map([box.x+(x-gx)*sx,box.y+box.height-(y-gy)*sy]));const width=Math.max(.9,FORMULA_PEN_WIDTH*Math.sqrt(Math.abs((m.a*m.d-m.b*m.c)*sx*sy)));
    record(points,width);
    const path=document.createElementNS(NS,'path');path.setAttribute('d',glyphs[char][i]);path.setAttribute('transform',`matrix(${sx} 0 0 ${-sy} ${box.x-gx*sx} ${box.y+box.height+gy*sy})`);path.setAttribute('fill','none');path.setAttribute('stroke',inkColor);path.setAttribute('stroke-width',String(FORMULA_PEN_WIDTH));path.setAttribute('stroke-linecap','round');path.setAttribute('stroke-linejoin','round');group.append(path);
   }element.replaceWith(group);
  }else if(fraction){
   const n=Math.max(4,Math.ceil(box.width/50)),local=Array.from({length:n+1},(_,i)=>[box.x+box.width*i/n,box.y+box.height*(.5+.16*Math.sin(i/n*Math.PI*2))]),mapped=local.map(map),width=Math.max(.9,box.height*Math.hypot(m.c,m.d)*.72);
   record(mapped,width);
   const path=document.createElementNS(NS,'path');path.setAttribute('d',local.map(([x,y],i)=>(i?'L':'M')+x+' '+y).join(' '));path.setAttribute('fill','none');path.setAttribute('stroke',inkColor);path.setAttribute('stroke-width',String(box.height*.72));path.setAttribute('stroke-linecap','round');element.replaceWith(path);
  }else{
   const rect=clipRect(pointBox([[box.x,box.y],[box.x+box.width,box.y],[box.x,box.y+box.height],[box.x+box.width,box.y+box.height]].map(map),1),clip);if(rect)operations.push({...semantic,rect});
  }
 }
 const data=new XMLSerializer().serializeToString(root),blob=URL.createObjectURL(new Blob([data],{type:'image/svg+xml'}));try{const image=await decodeImage(blob);image.authoredOperations=operations;return image;}finally{URL.revokeObjectURL(blob);}
 }finally{host.remove();}
}
