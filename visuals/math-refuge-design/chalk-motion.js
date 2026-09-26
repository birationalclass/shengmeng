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
  const s=plan.segments[lo],linear=clamp((t-s.start)/s.cost),f=s.curve===undefined?linear:linear*linear*(3-2*linear);
  return {x:s.a[0]+(s.b[0]-s.a[0])*f,y:Math.max(s.minY??-Infinity,Math.min(s.maxY??Infinity,s.a[1]+(s.b[1]-s.a[1])*f+(s.curve||0)*4*f*(1-f))),sway:0,contact:s.contact,lift:s.contact?0:.08*Math.sin(Math.PI*f),row:s.row,entering:s.entering,strokePoint:s.strokePoint};
}
export function writingPlan(rows,guides){
  const key=guides||rows;if(cache.has(key))return cache.get(key);
  const segments=[];let previous=null;
  rows.forEach(([x,y,w,h],row)=>{
    const path=rows[row].strokePath,start=segments.length;
    // One character has a fixed time budget, independent of its pixel size.
    const units=rows[row].writeUnits??(path?1:Math.max(1,w/Math.max(1,h)*1.8));
    const finish=()=>{const cost=segments.slice(start).reduce((sum,s)=>sum+s.cost,0);for(let i=start;i<segments.length;i++)segments[i].cost*=55*units/Math.max(.001,cost);};
    if(path){
      const first=path[0];
      segments.push({a:previous||first,b:first,cost:previous?Math.max(10,Math.hypot(first[0]-previous[0],first[1]-previous[1])/6):12,contact:false,row,entering:true});
      for(let i=0;i<path.length-1;i++)segments.push({a:path[i],b:path[i+1],cost:Math.max(1,Math.hypot(path[i+1][0]-path[i][0],path[i+1][1]-path[i][1])),contact:true,row,strokePoint:i});
      previous=path.at(-1);finish();return;
    }
    const g=guides?.[row],columns=g?(g.inkColumns||g.map((v,i)=>v===null?-1:i).filter(i=>i>=0)):Array.from({length:Math.ceil(w/5)+1},(_,i)=>i);
    if(!columns.length)return;
    const point=c=>[x+Math.min(w,c*5),g?g[c]:y+h*.55],first=point(columns[0]);
    segments.push({a:previous||first,b:first,cost:previous?Math.max(10,Math.hypot(first[0]-previous[0],first[1]-previous[1])/6):12,contact:false,row,entering:true});
    for(let i=0;i<columns.length;i++){
      const a=point(columns[i]),b=point(columns[Math.min(i+1,columns.length-1)]),gap=i+1<columns.length&&columns[i+1]-columns[i]>1;
      const distance=Math.hypot(b[0]-a[0],b[1]-a[1]);
      const chinese=(rows[row].chineseSpans||[]).some(([left,right])=>(a[0]+b[0])/2>=left&&(a[0]+b[0])/2<=right);
      segments.push({a,b,cost:Math.max(1,gap?distance/5:distance),contact:!gap,row});
    }
    previous=point(columns.at(-1));finish();
    for(let i=start;i<segments.length;i++){const s=segments[i],cx=(s.a[0]+s.b[0])/2;if(s.contact&&(rows[row].chineseSpans||[]).some(([left,right])=>cx>=left&&cx<=right))s.cost*=2;}
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
export function strokeReveal(rows,progress,row,guides){
  const path=rows[row].strokePath;if(!path)return [];
  if(progress>=1)return path;
  const p=writingPose(rows,progress,guides);
  if(row<p.row)return path;if(row>p.row||p.entering)return [];
  return [...path.slice(0,p.strokePoint+1),[p.x,p.y]];
}
// Group nearby ink into regions, then wipe in broad overlapping arm sweeps.
export function erasingPlan(imageData,rows=[]){
 const width=imageData?.width||1536,height=imageData?.height||640,cols=Math.ceil(width/32),bands=Math.ceil(height/28),occupied=new Set(),segments=[];
 for(let j=0;j<bands;j++)for(let i=0;i<cols;i++){
  const x=i*32,y=j*28;let ink=false;
  if(imageData){for(let py=y;py<Math.min(height,y+28)&&!ink;py++)for(let px=x;px<Math.min(width,x+32);px++)if(imageData.data[(py*width+px)*4+3]>=96){ink=true;break;}}
  if(!imageData||!ink)ink=rows.some(r=>(!imageData||r.strokePath)&&x<r[0]+r[2]&&x+32>r[0]&&y<r[1]+r[3]&&y+28>r[1]);
  if(ink)occupied.add(j*cols+i);
 }
 const regions=[];
 while(occupied.size){const first=occupied.values().next().value,queue=[first];occupied.delete(first);let left=cols,right=0,top=bands,bottom=0;
  for(let k=0;k<queue.length;k++){const i=queue[k]%cols,j=Math.floor(queue[k]/cols);left=Math.min(left,i);right=Math.max(right,i);top=Math.min(top,j);bottom=Math.max(bottom,j);
   for(let dy=-2;dy<=2;dy++)for(let dx=-3;dx<=3;dx++){const x=i+dx,y=j+dy,key=y*cols+x;if(x>=0&&x<cols&&y>=0&&y<bands&&occupied.has(key)){occupied.delete(key);queue.push(key);}}
  }regions.push({left,right,top,bottom});
 }
 regions.sort((a,b)=>a.top-b.top||a.left-b.left);let previous=null,row=0;
 for(const r of regions){const left=r.left*32+10,right=Math.min(width-10,r.right*32+22),span=right-left;
  const bow=span>=240?Math.min(80,span*.13):0;
  for(let y=r.top*28+14;y<=Math.min(height-14,r.bottom*28+14+bow+(bow?28:0));y+=28){
   const a=[row%2?right:left,y],b=[row%2?left:right,y];
   if(previous)segments.push({a:previous,b:a,cost:Math.max(10,Math.hypot(a[0]-previous[0],a[1]-previous[1])/2),curve:0,contact:false,row});
   segments.push({a,b,cost:Math.max(24,Math.hypot(span,bow*2)),curve:-bow,contact:true,row,minY:14,maxY:height-14});previous=b;row++;
  }
 }
 return plan(segments,450);
}
export function eraserPose(progress,width=1536,height=640,path){
 const p=sample(path||erasingPlan(null,[[32,18,width-64,height-36]]),progress);
 return {...p,angle:-.19};
}
export function wetOpacity(age){return .16*Math.pow(clamp(1-age/DRY_SECONDS),1.4);}
export function chalkLength(wear){return Math.max(.045,.17-Math.max(0,wear));}
