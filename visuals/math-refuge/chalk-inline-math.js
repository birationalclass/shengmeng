// Simple inline radicals share measured geometry with their reveal bounds.
// Full formulas use the prebuilt MathJax SVGs.
export function inlineInk(ctx,run,size){
 const ink=ctx.measureText(run.text);if(!run.radical)return ink;
 const width=size*.52+Math.max(ink.width,ink.actualBoundingBoxRight||0)+size*.12;
 const ascent=Math.max(size*.83,(ink.actualBoundingBoxAscent??size*.8)+size*.12);
 return {width,actualBoundingBoxLeft:0,actualBoundingBoxRight:width,actualBoundingBoxAscent:ascent+size*.026,actualBoundingBoxDescent:Math.max(ink.actualBoundingBoxDescent||0,size*.046)};
}
export function drawInlineInk(ctx,run,x,y,size){
 if(!run.radical){ctx.fillText(run.text,x,y);return;}
 const ink=inlineInk(ctx,run,size),top=y-ink.actualBoundingBoxAscent+size*.026;
 const points=[[x+size*.025,y-size*.28],[x+size*.14,y-size*.35],[x+size*.28,y+size*.02],[x+size*.49,top],[x+ink.width-size*.025,top]];
 const width=Math.max(1,size*.05),color=ctx.fillStyle;
 if(ctx.chalkStroke)ctx.chalkStroke(points,width,color);
 else{ctx.save();ctx.strokeStyle=color;ctx.lineWidth=width;ctx.lineCap='round';ctx.lineJoin='round';ctx.beginPath();points.forEach(([a,b],i)=>i?ctx.lineTo(a,b):ctx.moveTo(a,b));ctx.stroke();ctx.restore();}
 ctx.fillText(run.text,x+size*.52,y);
}
