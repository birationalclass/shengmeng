import {homepageStrokePlans} from './homepage-strokes.js';
const clamp=(x,a=0,b=1)=>Math.max(a,Math.min(b,x));
const D=1664,P=320;
function registeredPlan(medians,mask,n){
 const ink=[];for(let i=0;i<mask.length;i++)if(mask[i])ink.push([i%n,Math.floor(i/n)]);
 const points=(medians||[]).flat().map(([x,y])=>[x,900-y]);
 if(!points.length){const lo=Math.min(...ink.map(p=>p[1])),hi=Math.max(...ink.map(p=>p[1]));return [{name:'轮廓成形',points:[[512,(lo/n*D-P),35],[512,(hi/n*D-P),35]]}];}
 const box=p=>[Math.min(...p.map(v=>v[0])),Math.min(...p.map(v=>v[1])),Math.max(...p.map(v=>v[0])),Math.max(...p.map(v=>v[1]))],a=box(points),b=box(ink),padX=(b[2]-b[0])*.06,padY=(b[3]-b[1])*.055;
 return medians.map((line,i)=>({name:'第'+(i+1)+'笔',points:line.map(([x,y])=>[((b[0]+padX+(x-a[0])/Math.max(1,a[2]-a[0])*(b[2]-b[0]-2*padX))/n*D-P),((b[1]+padY+(900-y-a[1])/Math.max(1,a[3]-a[1])*(b[3]-b[1]-2*padY))/n*D-P),45])}));
}
function scheduled(strokes){
 let seconds=.04;
 const out=strokes.map((stroke,i)=>{const lengths=[0];for(let j=1;j<stroke.points.length;j++)lengths.push(lengths.at(-1)+Math.hypot(stroke.points[j][0]-stroke.points[j-1][0],stroke.points[j][1]-stroke.points[j-1][1]));const duration=clamp(.14+lengths.at(-1)*.00038,.16,.5),start=seconds,drawEnd=start+duration;seconds=drawEnd+.05;return {...stroke,index:i,lengths,length:lengths.at(-1),start,drawEnd,end:seconds};});
 seconds+=.04;for(const s of out){s.start/=seconds;s.drawEnd/=seconds;s.end/=seconds;}return {strokes:out,seconds};
}
// A point becomes ink only after the current brush footprint physically reaches
// it. The footprint is flood-filled through connected font ink, so it cannot
// jump a white gap and expose an unrelated stroke or a future detached dot.
export function buildStrokeDeposition(mask,n,medians,{character,field}={}){
 const authored=!!homepageStrokePlans[character],plan=scheduled(homepageStrokePlans[character]||registeredPlan(medians,mask,n)),birth=new Float32Array(n*n).fill(Infinity),owner=new Int16Array(n*n).fill(-1),across=new Float32Array(n*n),stamps=new Int32Array(n*n),queue=new Int32Array(n*n);let stamp=0,painted=0;
 const paint=(cx,cy,r,time,which,dx,dy)=>{
  const left=Math.max(0,Math.floor(cx-r-1)),right=Math.min(n-1,Math.ceil(cx+r+1)),top=Math.max(0,Math.floor(cy-r-1)),bottom=Math.min(n-1,Math.ceil(cy+r+1));let seed=-1,best=Infinity;
  for(let y=top;y<=bottom;y++)for(let x=left;x<=right;x++){const d=(x+.5-cx)**2+(y+.5-cy)**2;if(mask[y*n+x]&&d<best&&d<=r*r){seed=y*n+x;best=d;}}
  if(seed<0)return;
  // A broad belly can extend beyond a hand-placed radius, but this local
  // widening remains bounded and cannot reach across a separate ink island.
  r=Math.max(r,Math.min(r*1.45,(field?.[seed]||0)+1.2));
  let head=0,tail=0;queue[tail++]=seed;stamps[seed]=++stamp;
  while(head<tail){const id=queue[head++],x=id%n,y=Math.floor(id/n);if(!Number.isFinite(birth[id])){birth[id]=time;owner[id]=which;across[id]=((x+.5-cx)*dy-(y+.5-cy)*dx)/Math.max(1,Math.hypot(dx,dy))/5;painted++;}
   for(let yy=Math.max(0,y-1);yy<=Math.min(n-1,y+1);yy++)for(let xx=Math.max(0,x-1);xx<=Math.min(n-1,x+1);xx++){const k=yy*n+xx;if(stamps[k]===stamp||!mask[k]||(xx+.5-cx)**2+(yy+.5-cy)**2>r*r)continue;stamps[k]=stamp;queue[tail++]=k;}
  }
 };
 for(const s of plan.strokes)for(let j=1;j<s.points.length;j++){
  const a=s.points[j-1],b=s.points[j],dx=b[0]-a[0],dy=b[1]-a[1],distance=Math.hypot(dx,dy),steps=Math.max(1,Math.ceil(distance*n/D/.7));
  for(let k=0;k<=steps;k++){const t=k/steps,u=(s.lengths[j-1]+distance*t)/Math.max(1,s.length),x=(a[0]+dx*t+P)*n/D,y=(a[1]+dy*t+P)*n/D,r=Math.max(.35,(a[2]+(b[2]-a[2])*t)*n/D);paint(x,y,r,s.start+(s.drawEnd-s.start)*u,s.index,dx,dy);}
 }
 // Fill only the remaining edge band through already connected ink. Large
 // unmatched regions are reported for the authored-plan visual audit.
 const distance=new Uint16Array(n*n);let head=0,tail=0;
 for(let i=0;i<mask.length;i++)if(mask[i]&&Number.isFinite(birth[i]))queue[tail++]=i;
 let maxEdgeFill=0,filled=0;
 while(head<tail){const id=queue[head++],x=id%n,y=Math.floor(id/n);for(let yy=Math.max(0,y-1);yy<=Math.min(n-1,y+1);yy++)for(let xx=Math.max(0,x-1);xx<=Math.min(n-1,x+1);xx++){const k=yy*n+xx;if(!mask[k]||Number.isFinite(birth[k]))continue;distance[k]=distance[id]+1;maxEdgeFill=Math.max(maxEdgeFill,distance[k]);birth[k]=birth[id];owner[k]=owner[id];across[k]=across[id];queue[tail++]=k;filled++;}}
 const missing=[];for(let i=0;i<mask.length;i++)if(mask[i]&&!Number.isFinite(birth[i]))missing.push(i);
 for(const id of missing){birth[id]=plan.strokes.at(-1).drawEnd;owner[id]=plan.strokes.length-1;}
 return {...plan,authored,character,birth,owner,across,mask,audit:{inkPixels:painted+filled+missing.length,paintedPixels:painted,edgePixels:filled,maxEdgeFill,unreachedPixels:missing.length,unreachedPoints:missing.slice(0,16).map(id=>[(id%n+.5)/n*D-P,(Math.floor(id/n)+.5)/n*D-P])}};
}
