const pick=(value,language)=>Array.isArray(value)?value[language==='en'?1:0]:value;
export const CHALK_SEMANTIC_COLORS={conclusion:'#93c9ff',caution:'#ffada3'};
// Exact paths from the course homepage's lesson-1/screen.js.
export const REFERENCE_ICON_PATHS={textbook:['M12 5.5C9 3.6 5.5 3.5 2.5 4.5v14c3-1 6.5-.9 9.5 1 3-1.9 6.5-2 9.5-1v-14c-3-1-6.5-.9-9.5 1Z','M12 5.5v14'],extension:['M9 5V4a3 3 0 0 1 6 0v1h4a1 1 0 0 1 1 1v4h-1a3 3 0 0 0 0 6h1v4a1 1 0 0 1-1 1h-4v-1a3 3 0 0 0-6 0v1H5a1 1 0 0 1-1-1v-4H3a3 3 0 0 1 0-6h1V6a1 1 0 0 1 1-1Z']};
const iconSamples=new Map();
export function classroomHeading(page,language,title){return page.classroom&&page.topic?pick(page.topic,language)+' — '+pick(page.subtitle,language):title;}
// Preserve source records, but display only references not already on this board.
export function classroomReferenceCaption(page,language='zh'){
 if(page.statementOnly||page.reference?.kind!=='textbook')return '';
 const normalize=s=>String(s||'').replace(/Corollary/gi,'推论').replace(/\s/g,'');
 const ink=normalize([page.title,page.enTitle,page.en?.title,...(page.boardLines||page.lines||[]).flatMap(l=>[l.text,l.enText])].filter(Boolean).join(' '));
 return String(pick(page.reference.label,language)||'').split(/[；;]/).filter(part=>{const ids=normalize(part).match(/\d+\.\d+\.\d+|推论\d+/g)||[];return !ids.length||!ids.every(id=>ink.includes(id));}).map(s=>s.trim()).join(language==='en'?'; ':'；');
}
export function drawReferenceIcon(ctx,kind,x,y,size=22){
 const paths=REFERENCE_ICON_PATHS[kind]||REFERENCE_ICON_PATHS.extension,k=size/24;
 if(typeof ctx.chalkStroke==='function'&&typeof document!=='undefined'){
  if(!iconSamples.has(kind))iconSamples.set(kind,paths.map(d=>{const p=document.createElementNS('http://www.w3.org/2000/svg','path');p.setAttribute('d',d);const length=p.getTotalLength(),n=Math.ceil(length*2);return Array.from({length:n+1},(_,i)=>{const a=p.getPointAtLength(length*i/n);return[a.x,a.y];});}));
  for(const points of iconSamples.get(kind))ctx.chalkStroke(points.map(([a,b])=>[x+a*k,y+b*k]),1.5*k,ctx.fillStyle);
 }else if(typeof Path2D!=='undefined'){
  ctx.save();ctx.translate(x,y);ctx.scale(k,k);ctx.lineWidth=1.5;ctx.lineCap='round';ctx.lineJoin='round';ctx.strokeStyle=ctx.fillStyle;for(const d of paths)ctx.stroke(new Path2D(d));ctx.restore();
 }
}
// Automatic overlays are deliberately outside the chalk/erase raster.
export function drawClassroomMetadata(ctx,page,index,language,{exercise=false,total=40}={}){
 ctx.save();ctx.fillStyle='#eee9d5';ctx.textBaseline='alphabetic';ctx.font='18px "Microsoft YaHei", "Segoe UI", sans-serif';ctx.globalAlpha=.32;ctx.textAlign='right';ctx.fillText(language==='en'?'Page '+(index+1)+' / '+total:'第 '+(index+1)+' / '+total+' 页',1470,625);
 if(!page.classroom){ctx.restore();return;}ctx.fillText(page.source||'§2.6',1470,28);
 if(!page.kind&&!exercise){const caption=classroomReferenceCaption(page,language);ctx.textAlign='left';ctx.globalAlpha=.58;if(caption)ctx.fillText(caption,84,29);
 }
 ctx.restore();
}
