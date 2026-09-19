export const ERASE_PASSES=14,DRY_SECONDS=12,ERASER_HALF_WIDTH=47,ERASER_HALF_HEIGHT=28;
const clamp=x=>Math.max(0,Math.min(1,x));
const ease=x=>x*x*(3-2*x);
export function rowReveal(progress,row,count){return clamp((progress*count-row-.08)/.92);}
// Sample visible ink columns. This follows the displayed SVG, not a recovered
// pen-stroke order; disconnected glyphs cause a small pen lift.
export function inkGuides(imageData,rows){
  return rows.map(([x,y,w,h])=>{
    const samples=[];let previous=y+h*.55;
    for(let column=0;column<=Math.ceil(w/5);column++){
      const px=Math.min(imageData.width-1,Math.round(x+Math.min(w,column*5)));let best=null,cost=Infinity;
      for(let py=Math.max(0,Math.floor(y));py<Math.min(imageData.height,y+h);py++){
        const alpha=imageData.data[(py*imageData.width+px)*4+3];
        if(alpha<96)continue;const d=Math.abs(py-previous)+Math.abs(py-y-h*.55)*.08;
        if(d<cost){cost=d;best=py;}
      }
      samples.push(best);if(best!==null)previous=best;
    }
    return samples;
  });
}
export function writingPose(rows,progress,guides){
  const t=clamp(progress)*rows.length,row=Math.min(rows.length-1,Math.floor(t)),f=t-row,[x,y,w,h]=rows[row],reveal=rowReveal(progress,row,rows.length);
  let px=x+w*reveal,py=y+h*.55,contact=f>=.08,lift=0;
  const samples=guides?.[row];
  if(samples){const at=Math.min(samples.length-1,Math.floor(w*reveal/5)),ink=samples[at];if(ink===null)contact=false;else py=ink;}
  if(f<.08){
    const prior=rows[Math.max(0,row-1)],q=ease(f/.08);
    px=prior[0]+prior[2]+(x-prior[0]-prior[2])*q;py=prior[1]+prior[3]*.55+(py-prior[1]-prior[3]*.55)*q;lift=Math.sin(q*Math.PI)*.16;contact=false;
  }
  return {x:px,y:py,contact,lift,row,reveal};
}
export function eraserPose(progress,width=1536,height=640){
  const t=clamp(progress)*ERASE_PASSES,row=Math.min(ERASE_PASSES-1,Math.floor(t)),f=t-row;
  const q=ease(Math.min(1,f/.86)),turn=clamp((f-.86)/.14),left=32,right=width-32;
  return {x:row%2?right-(right-left)*q:left+(right-left)*q,
    y:18+(row+Math.min(1,ERASE_PASSES-1-row)*ease(turn))*(height-36)/(ERASE_PASSES-1)+Math.sin(q*Math.PI)*3,
    angle:-.19+Math.sin(t*1.7)*.045,contact:f<=.86||row===ERASE_PASSES-1,lift:Math.sin(turn*Math.PI)*.045,row};
}
export function wetOpacity(age){return .16*Math.pow(clamp(1-age/DRY_SECONDS),1.4);}
export function chalkLength(wear){return Math.max(.045,.17-Math.max(0,wear));}
