import {ERASER_ANGLE,FELT_HALF_WIDTH,FELT_HALF_HEIGHT,feltCoreBounds} from './eraser-contact.js';
export const ERASE_PASSES=14,DRY_SECONDS=12,ERASER_HALF_WIDTH=FELT_HALF_WIDTH,ERASER_HALF_HEIGHT=FELT_HALF_HEIGHT;
const clamp=x=>Math.max(0,Math.min(1,x));
const cache=new WeakMap();
export const LETTER_SECONDS=.25,ERASER_SPEED=468,ERASER_TRANSFER_SPEED=936;
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
    // A padded 3px delimiter can lie entirely between the 5px samples.
    // Recover its actual ink instead of omitting it from the writing clock.
    if(samples.every(v=>v===null)){
      samples.length=0;samples.xs=[];
      for(let px=Math.max(0,Math.ceil(x));px<Math.min(imageData.width,x+w);px++){
        let best=null,cost=Infinity;
        for(let py=Math.max(0,Math.floor(y));py<Math.min(imageData.height,y+h);py++){
          if(imageData.data[(py*imageData.width+px)*4+3]<96)continue;
          const d=Math.abs(py-y-h*.55);if(d<cost){cost=d;best=py;}
        }
        samples.push(best);samples.xs.push(px-x);
      }
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
  return {x:s.a[0]+(s.b[0]-s.a[0])*f,y:Math.max(s.minY??-Infinity,Math.min(s.maxY??Infinity,s.a[1]+(s.b[1]-s.a[1])*f+(s.curve||0)*4*f*(1-f))),sway:0,contact:s.contact,lift:s.contact?0:.08*Math.sin(Math.PI*f),toolLift:s.liftHeight===undefined?undefined:s.liftHeight*Math.sin(Math.PI*linear)**2,row:s.row,entering:s.entering,strokePoint:s.strokePoint,strokeProgress:s.strokeFrom===undefined?undefined:s.strokeFrom+(s.strokeTo-s.strokeFrom)*f};
}
export function writingPlan(rows,guides){
  const key=guides||rows;if(cache.has(key))return cache.get(key);
  const segments=[];let previous=null;
  rows.forEach(([x,y,w,h],row)=>{
    const path=rows[row].strokePath;
    if(path){
      const first=path[0];
      const seconds=rows[row].strokeSeconds||rows[row].letterSeconds;
      const distance=previous?Math.hypot(first[0]-previous[0],first[1]-previous[1]):0;
      const sameGlyph=row>0&&(rows[row].strokeRaster?.group?rows[row].strokeRaster.group===rows[row-1].strokeRaster?.group:rows[row].letterGroup&&rows[row].letterGroup===rows[row-1].letterGroup);
      const moveSeconds=previous?Math.max(sameGlyph?.035:.065,Math.min(.5,distance/900)):.012;
      segments.push({a:previous||first,b:first,cost:230*moveSeconds,contact:false,row,entering:true,curve:0,liftHeight:previous?(sameGlyph?.006:.018):0});
      const lengths=path.slice(1).map((b,i)=>Math.hypot(b[0]-path[i][0],b[1]-path[i][1])),length=lengths.reduce((a,b)=>a+b,0);let arc=0;
      for(let i=0;i<path.length-1;i++){const from=length?arc/length:i/(path.length-1);arc+=lengths[i];const to=length?arc/length:(i+1)/(path.length-1);segments.push({a:path[i],b:path[i+1],cost:seconds?Math.max(1e-8,230*seconds*(to-from)):Math.max(1,lengths[i]),contact:true,row,strokePoint:i,strokeFrom:seconds?from:undefined,strokeTo:seconds?to:undefined,liftHeight:0});}
      previous=path.at(-1);return;
    }
    const g=guides?.[row],columns=g?(g.inkColumns||g.map((v,i)=>v===null?-1:i).filter(i=>i>=0)):Array.from({length:Math.ceil(w/5)+1},(_,i)=>i);
    if(!columns.length)return;
    const point=c=>[x+(g?.xs?.[c]??Math.min(w,c*5)),g?g[c]:y+h*.55],first=point(columns[0]);
    segments.push({a:previous||first,b:first,cost:230*(previous?Math.max(.065,Math.min(.5,Math.hypot(first[0]-previous[0],first[1]-previous[1])/900)):.012),contact:false,row,entering:true,curve:0,liftHeight:previous?.018:0});
    for(let i=0;i<columns.length;i++){
      const a=point(columns[i]),b=point(columns[Math.min(i+1,columns.length-1)]),gap=i+1<columns.length&&columns[i+1]-columns[i]>1;
      const distance=Math.hypot(b[0]-a[0],b[1]-a[1]);
      const chinese=(rows[row].chineseSpans||[]).some(([left,right])=>(a[0]+b[0])/2>=left&&(a[0]+b[0])/2<=right);
      segments.push({a,b,cost:gap?230*Math.max(.035,Math.min(.5,distance/900)):Math.max(1,distance)*(chinese?2:1),contact:!gap,row,...(gap?{curve:0,liftHeight:.006}:{liftHeight:0})});
    }
    previous=point(columns.at(-1));
  });
  for(const s of segments)s.mainLine=rows[s.row].mainLine;
  const result=plan(segments,230);result.chineseStrokeTiming=rows.some(r=>r.strokeRaster);result.letterTiming=rows.some(r=>r.letterSeconds);result.physicalTiming=result.chineseStrokeTiming||result.letterTiming;result.unitsPerSecond=230;cache.set(key,result);return result;
}
export const writingPose=(rows,progress,guides)=>sample(writingPlan(rows,guides),progress);
export function inkReveal(rows,progress,row,guides,pose){
  if(progress>=1)return rows[row][2];
  const p=pose||writingPose(rows,progress,guides);
  if(row<p.row)return rows[row][2];if(row>p.row||p.entering)return 0;
  return Math.max(0,Math.min(rows[row][2],p.x-rows[row][0]+5));
}
export function strokeReveal(rows,progress,row,guides,pose){
  const path=rows[row].strokePath;if(!path)return [];
  if(progress>=1)return path;
  const p=pose||writingPose(rows,progress,guides);
  if(row<p.row)return path;if(row>p.row||p.entering)return [];
  return [...path.slice(0,p.strokePoint+1),[p.x,p.y]];
}
export function rasterStrokeReveal(rows,progress,row,guides,pose){
 if(progress>=1)return 1;const p=pose||writingPose(rows,progress,guides);
 if(row<p.row)return 1;if(row>p.row||p.entering)return 0;return p.strokeProgress??0;
}
// Follow actual horizontal ink bands; never merge different text lines into
// one full-board rectangle. A real raster takes precedence over stroke boxes.
export function erasingPlan(imageData,rows=[]){
 const width=imageData?.width||1536,height=imageData?.height||640,segments=[],occupiedRows=new Uint8Array(height),angle=ERASER_ANGLE;
 const inkAt=(x,y)=>imageData?imageData.data[(y*width+x)*4+3]>=16:rows.some(r=>x>=r[0]&&x<r[0]+r[2]&&y>=r[1]&&y<r[1]+r[3]);
 for(let y=0;y<height;y++)for(let x=0;x<width;x++)if(inkAt(x,y)){occupiedRows[y]=1;break;}
 // Every band fits inside the fully opaque core of the actual soft felt mask.
 const {x:safeX,y:safeY}=feltCoreBounds(angle);
 let previous=null,row=0;
 for(let top=0;top<height;){
  while(top<height&&!occupiedRows[top])top++;if(top>=height)break;
  const bottom=Math.min(height-1,top+safeY*2),columns=new Uint8Array(width),center=top+safeY;
  for(let y=top;y<=bottom;y++)for(let x=0;x<width;x++)if(inkAt(x,y))columns[x]=1;
  const runs=[];let left=-1,last=-1;
  for(let x=0;x<width;x++)if(columns[x]){if(left<0)left=x;else if(x-last>ERASER_HALF_WIDTH*2){runs.push([left,last]);left=x;}last=x;}
  if(left>=0)runs.push([left,last]);if(row%2)runs.reverse();
  for(const [left,right]of runs){const narrow=right-left<safeX*2,start=narrow?(left+right)/2:left+safeX,end=narrow?start:right-safeX;
   const a=[row%2?end:start,center],b=[row%2?start:end,center];
   if(previous)segments.push({a:previous,b:a,cost:Math.max(360*.08,Math.hypot(a[0]-previous[0],a[1]-previous[1])*ERASER_SPEED/ERASER_TRANSFER_SPEED),contact:false,row});
   segments.push({a,b,cost:Math.max(360*.22,Math.abs(end-start)),contact:true,row});previous=b;
  }row++;top=bottom+1;
 }
 const result=plan(segments,ERASER_SPEED);result.duration=segments.length?Math.max(6/1.3,result.duration):.2;result.angle=angle;result.speed=ERASER_SPEED;return result;
}
export function eraserPose(progress,width=1536,height=640,path){
 const p=sample(path||erasingPlan(null,[[32,18,width-64,height-36]]),progress);
 return {...p,angle:path?.angle??ERASER_ANGLE};
}
export function wetOpacity(age){return .16*Math.pow(clamp(1-age/DRY_SECONDS),1.4);}
export function chalkLength(wear){return Math.max(.045,.17-Math.max(0,wear));}
