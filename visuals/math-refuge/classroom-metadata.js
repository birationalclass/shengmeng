const pick=(value,language)=>Array.isArray(value)?value[language==='en'?1:0]:value;
export const CHALK_SEMANTIC_COLORS={conclusion:'#93c9ff',caution:'#ffada3'};
// Exact paths from the course homepage's lesson-1/screen.js.
export const REFERENCE_ICON_PATHS={exercise:["M9 18h6M9.5 21h5M8.5 15.5C8.5 13 5.5 12 5.5 8a6.5 6.5 0 0 1 13 0c0 4-3 5-3 7.5V17h-7Z","M12 1V0M3 3 1.5 1.5M21 3l1.5-1.5M3 9H1M21 9h2"],textbook:['M12 5.5C9 3.6 5.5 3.5 2.5 4.5v14c3-1 6.5-.9 9.5 1 3-1.9 6.5-2 9.5-1v-14c-3-1-6.5-.9-9.5 1Z','M12 5.5v14'],extension:['M9 5V4a3 3 0 0 1 6 0v1h4a1 1 0 0 1 1 1v4h-1a3 3 0 0 0 0 6h1v4a1 1 0 0 1-1 1h-4v-1a3 3 0 0 0-6 0v1H5a1 1 0 0 1-1-1v-4H3a3 3 0 0 1 0-6h1V6a1 1 0 0 1 1-1Z']};
const iconSamples=new Map();
// SVG move commands lift the pen. Sampling a compound path as one polyline
// would draw bridges between the bulb's separate rays, outline and base.
export function referenceIconStrokePaths(kind){
 return (REFERENCE_ICON_PATHS[kind]||REFERENCE_ICON_PATHS.extension).flatMap(d=>{
  if(/m/.test(d))throw Error('Reference icons must use absolute M moves');
  return d.match(/M[^M]*/g)||[];
 });
}
export function classroomHeading(page,language,title){return page.classroom&&page.topic?pick(page.topic,language)+' — '+pick(page.subtitle,language):title;}
// Preserve source records, but display only references not already on this board.
export function classroomReferenceCaption(){return '';}
export function drawReferenceIcon(ctx,kind,x,y,size=22){
 const paths=REFERENCE_ICON_PATHS[kind]||REFERENCE_ICON_PATHS.extension,k=size/24;
 if(typeof ctx.chalkStroke==='function'&&typeof document!=='undefined'){
  if(!iconSamples.has(kind))iconSamples.set(kind,referenceIconStrokePaths(kind).map(d=>{const p=document.createElementNS('http://www.w3.org/2000/svg','path');p.setAttribute('d',d);const length=p.getTotalLength(),n=Math.max(1,Math.ceil(length*2));return Array.from({length:n+1},(_,i)=>{const a=p.getPointAtLength(length*i/n);return[a.x,a.y];});}));
  for(const points of iconSamples.get(kind))ctx.chalkStroke(points.map(([a,b])=>[x+a*k,y+b*k]),1.5*k,ctx.fillStyle);
 }else if(typeof Path2D!=='undefined'){
  ctx.save();ctx.translate(x,y);ctx.scale(k,k);ctx.lineWidth=1.5;ctx.lineCap='round';ctx.lineJoin='round';ctx.strokeStyle=ctx.fillStyle;for(const d of paths)ctx.stroke(new Path2D(d));ctx.restore();
 }
}
// Automatic overlays are deliberately outside the chalk/erase raster.
export const WATERMARK_FONT_SIZE=54,WATERMARK_OPACITY=.10,WATERMARK_INSET=32;
export function watermarkAnchor(metrics,{left=false,top=false,width=1536,height=640}={}){
 const ascent=metrics.actualBoundingBoxAscent??WATERMARK_FONT_SIZE*.78,descent=metrics.actualBoundingBoxDescent??WATERMARK_FONT_SIZE*.22;
 return{x:left?WATERMARK_INSET+(metrics.actualBoundingBoxLeft??0):width-WATERMARK_INSET-(metrics.actualBoundingBoxRight??metrics.width??0),y:top?WATERMARK_INSET+ascent:height-WATERMARK_INSET-descent};
}
export function drawClassroomMetadata(ctx,page,index,language,{exercise=false,total=40}={}){
 if(page.period==='break')return;
 ctx.save();ctx.fillStyle='#eee9d5';ctx.textBaseline='alphabetic';ctx.font=WATERMARK_FONT_SIZE+'px "Microsoft YaHei", "Segoe UI", sans-serif';ctx.globalAlpha=WATERMARK_OPACITY;ctx.textAlign='left';
 const label=(text,options)=>{const p=watermarkAnchor(ctx.measureText?.(text)||{},options);ctx.fillText(text,p.x,p.y);};
 label((index+1)+' / '+total,{left:exercise||page.exerciseBoard});
 if(page.classroom)label(page.source||'§2.6',{top:true});ctx.restore();
}
