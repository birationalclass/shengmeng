export const ERASE_PASSES=14,DRY_SECONDS=12,ERASER_HALF_WIDTH=47,ERASER_HALF_HEIGHT=28;
const clamp=x=>Math.max(0,Math.min(1,x));
const cache=new WeakMap();
export function rowReveal(progress,row,count){return clamp(progress*count-row);}
// Sample the displayed ink, not a reconstructed handwriting stroke order.
export function inkGuides(imageData,rows){
  return rows.map(([x,y,w,h])=>{
    const samples=[];let previous=y+h*.55;
    for(let column=0;column<=Math.ceil(w/5);column++){
      const px=Math.min(imageData.width-1,Math.round(x+Math.min(w,column*5)));let best=null,cost=Infinity;
      for(let py=Math.max(0,Math.floor(y));py<Math.min(imageData.height,y+h);py++){
        if(imageData.data[(py*imageData.width+px)*4+3]<96)continue;
        const d=Math.abs(py-previous)+Math.abs(py-y-h*.55)*.08;
        if(d<cost){cost=d;best=py;}
      }
      samples.push(best);if(best!==null)previous=best;
    }
    samples.inkColumns=samples.map((v,i)=>v===null?-1:i).filter(i=>i>=0);return samples;
  });
}
function plan(segments,speed){
  let total=0;for(const s of segments){s.start=total;total+=s.cost;s.end=total;}
  return {segments,total,duration:Math.max(.2,total/speed)};
}
function sample(plan,progress){
  if(!plan.segments.length)return {x:0,y:0,contact:false,lift:.1,row:0};
  const t=clamp(progress)*plan.total;let lo=0,hi=plan.segments.length-1;
  while(lo<hi){const mid=(lo+hi)>>1;if(plan.segments[mid].end<t)lo=mid+1;else hi=mid;}
  const s=plan.segments[lo],f=clamp((t-s.start)/s.cost);
  return {x:s.a[0]+(s.b[0]-s.a[0])*f,y:s.a[1]+(s.b[1]-s.a[1])*f,contact:s.contact,lift:s.contact?0:.08*Math.sin(Math.PI*f),row:s.row,entering:s.entering};
}
export function writingPlan(rows,guides){
  const key=guides||rows;if(cache.has(key))return cache.get(key);
  const segments=[];let previous=null;
  rows.forEach(([x,y,w,h],row)=>{
    const g=guides?.[row],columns=g?(g.inkColumns||g.map((v,i)=>v===null?-1:i).filter(i=>i>=0)):Array.from({length:Math.ceil(w/5)+1},(_,i)=>i);
    if(!columns.length)return;
    const point=c=>[x+Math.min(w,c*5),g?g[c]:y+h*.55],first=point(columns[0]);
    segments.push({a:previous||first,b:first,cost:previous?Math.max(10,Math.hypot(first[0]-previous[0],first[1]-previous[1])/6):12,contact:false,row,entering:true});
    for(let i=0;i<columns.length;i++){
      const a=point(columns[i]),b=point(columns[Math.min(i+1,columns.length-1)]),gap=i+1<columns.length&&columns[i+1]-columns[i]>1;
      const distance=Math.hypot(b[0]-a[0],b[1]-a[1]);
      segments.push({a,b,cost:Math.max(1,gap?distance/5:distance),contact:!gap,row});
    }
    previous=point(columns.at(-1));
  });
  const result=plan(segments,230);cache.set(key,result);return result;
}
export const writingPose=(rows,progress,guides)=>sample(writingPlan(rows,guides),progress);
export function inkReveal(rows,progress,row,guides){
  if(progress>=1)return rows[row][2];
  const p=writingPose(rows,progress,guides);
  if(row<p.row)return rows[row][2];if(row>p.row||p.entering)return 0;
  return Math.max(0,Math.min(rows[row][2],p.x-rows[row][0]+5));
}
// Occupied 32 x 28 px tiles define short horizontal wipes. Empty regions
// cause lifted travel, never a full-row wipe across the entire blackboard.
export function erasingPlan(imageData,rows=[]){
  const width=imageData?.width||1536,height=imageData?.height||640,segments=[];
  let previous=null;
  for(let y=0,band=0;y<height;y+=28,band++){
    const occupied=[];
    for(let x=0;x<width;x+=32){
      let ink=false;
      if(imageData){
        for(let py=y;py<Math.min(height,y+28)&&!ink;py++)for(let px=x;px<Math.min(width,x+32);px++)if(imageData.data[(py*width+px)*4+3]>=96){ink=true;break;}
      }else ink=rows.some(([a,b,w,h])=>x<a+w&&x+32>a&&y<b+h&&y+28>b);
      occupied.push(ink);
    }
    const runs=[];
    for(let i=0;i<occupied.length;i++)if(occupied[i]){const start=i;while(occupied[i+1])i++;runs.push([start,i]);}
    if(band%2)runs.reverse();
    for(const [left,right] of runs){
      const a=[(band%2?right:left)*32+16,Math.min(height-1,y+14)],b=[(band%2?left:right)*32+16,Math.min(height-1,y+14)];
      if(previous)segments.push({a:previous,b:a,cost:Math.max(10,Math.hypot(a[0]-previous[0],a[1]-previous[1])/4),contact:false,row:band});
      segments.push({a,b,cost:Math.max(24,Math.abs(b[0]-a[0])),contact:true,row:band});previous=b;
    }
  }
  return plan(segments,450);
}
export function eraserPose(progress,width=1536,height=640,path){
  const p=sample(path||erasingPlan(null,[[32,18,width-64,height-36]]),progress);
  return {...p,angle:-.19+Math.sin(progress*9)*.035};
}
export function wetOpacity(age){return .16*Math.pow(clamp(1-age/DRY_SECONDS),1.4);}
export function chalkLength(wear){return Math.max(.045,.17-Math.max(0,wear));}
