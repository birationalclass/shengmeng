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
    samples.inkColumns=samples.map((v,i)=>v===null?-1:i).filter(i=>i>=0);
    return samples;
  });
}
export function writingPose(rows,progress,guides){
  const t=clamp(progress)*rows.length,row=Math.min(rows.length-1,Math.floor(t)),f=t-row,[x,y,w,h]=rows[row],reveal=rowReveal(progress,row,rows.length);
  let px=x+w*reveal,py=y+h*.55,contact=f>=.08,lift=0;
  const samples=guides?.[row];
  if(samples){
    const columns=samples.inkColumns||samples.map((v,i)=>v===null?-1:i).filter(i=>i>=0);
    if(!columns.length){contact=false;px=x;}
    else{
      const q=reveal*Math.max(0,columns.length-1),i=Math.floor(q),a=columns[i],b=columns[Math.min(i+1,columns.length-1)],f=q-i;
      px=x+Math.min(w,(a+(b-a)*f)*5);py=samples[a]+(samples[b]-samples[a])*f;
      if(b-a>1&&f>.02&&f<.98){contact=false;lift=Math.sin(f*Math.PI)*.09;}
    }
  }
  if(f<.08){
    const prior=rows[Math.max(0,row-1)],previous=guides?.[Math.max(0,row-1)],columns=previous?.inkColumns,q=ease(f/.08);
    const end=prior[0]+(columns?.length?columns.at(-1)*5:prior[2]),start=px;
    px=end+(start-end)*q;py=prior[1]+prior[3]*.55+(py-prior[1]-prior[3]*.55)*q;lift=Math.sin(q*Math.PI)*.16;contact=false;
  }
  return {x:px,y:py,contact,lift,row,reveal};
}
// Texture reveal and tool position share the same ink-only progression.
export function inkReveal(rows,progress,row,guides){
  if(progress*rows.length>=row+1)return rows[row][2];
  if(progress*rows.length<row+.08)return 0;
  return Math.max(0,writingPose(rows,progress,guides).x-rows[row][0]+5);
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
