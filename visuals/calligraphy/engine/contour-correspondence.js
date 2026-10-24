// Monotone advancing-point correspondence for two independently drawn edges.
// It changes only which points are paired; neither contour is projected or
// offset. This is our numerical implementation, not the author's source code.
const clamp=x=>Math.max(0,Math.min(1,x));
const dist=(a,b)=>Math.hypot(a.x-b.x,a.y-b.y);
function monotone(values,u){
 // A clamped cubic B-spline of monotone scalar controls remains monotone
 // and is C2. Piecewise Hermite maps left visible acceleration chatter.
 u=clamp(u);const n=values.length,p=3,k=u===1?n-1:Math.min(n-1,p+Math.floor(u*(n-p))),
  knot=i=>i<=p?0:i>=n?1:(i-p)/(n-p),d=Array.from({length:p+1},(_,j)=>values[k-p+j]);
 for(let r=1;r<=p;r++)for(let j=p;j>=r;j--){const i=k-p+j,den=knot(i+p-r+1)-knot(i),a=den?(u-knot(i))/den:0;d[j]=d[j-1]*(1-a)+d[j]*a;}
 return d[p];
}
function arcSamples(curve,count){
 const dense=800,points=Array.from({length:dense+1},(_,i)=>curve(i/dense)),arc=[0];
 for(let i=1;i<=dense;i++)arc.push(arc.at(-1)+dist(points[i],points[i-1]));
 const total=arc.at(-1),samples=[],parameters=[];let cursor=0;
 for(let i=0;i<=count;i++){
  const target=total*i/count;while(cursor<dense-1&&arc[cursor+1]<target)cursor++;
  const t=(cursor+(target-arc[cursor])/Math.max(1e-12,arc[cursor+1]-arc[cursor]))/dense;
  samples.push(curve(t));parameters.push(t);
 }
 return {samples,parameters,total};
}
function inside(p,polygon){
 let result=false;
 for(let i=0,j=polygon.length-1;i<polygon.length;j=i++){
  const a=polygon[i],b=polygon[j];
  if((a.y>p.y)!==(b.y>p.y)&&p.x<(b.x-a.x)*(p.y-a.y)/(b.y-a.y)+a.x)result=!result;
 }
 return result;
}
export function pairBoundaryCurves(curveA,curveB,count=160){
 const a=arcSamples(curveA,count),b=arcSamples(curveB,count),size=count+1,
  polygon=[...a.samples,...b.samples.slice().reverse()],costs=new Float64Array(size*size),
  score=new Float64Array(size*size).fill(Infinity),step=new Uint8Array(size*size);
 const scale=Math.max(a.total,b.total),penalty=scale*scale*.20;
 for(let i=0;i<size;i++)for(let j=0;j<size;j++){
  const p=a.samples[i],q=b.samples[j],dx=q.x-p.x,dy=q.y-p.y,d2=dx*dx+dy*dy;
  let value=d2;
  if(d2>scale*scale*.00002&&!inside({x:(p.x+q.x)*.5,y:(p.y+q.y)*.5},polygon))value+=penalty;
  costs[i*size+j]=value;
 }
 const wa=a.total/Math.max(1e-12,a.total+b.total),wb=1-wa;score[0]=0;
 for(let i=0;i<size;i++)for(let j=0;j<size;j++){
  if(i===0&&j===0)continue;const at=i*size+j,c=costs[at];let best=Infinity,move=0;
  for(const [di,dj,type,w] of [[1,1,1,1],[1,0,2,wa],[0,1,3,wb]]){
   if(i<di||j<dj)continue;const prior=(i-di)*size+j-dj,candidate=score[prior]+(c+costs[prior])*.5*w;
   if(candidate<best){best=candidate;move=type;}
  }
  score[at]=best;step[at]=move;
 }
 const path=[];let i=count,j=count;
 while(i||j){path.push([i,j]);const move=step[i*size+j];if(move===1){i--;j--;}else if(move===2)i--;else j--;}
 path.push([0,0]);path.reverse();
 const arc=[0];for(let k=1;k<path.length;k++)arc.push(arc.at(-1)+(path[k][0]-path[k-1][0])*wa+(path[k][1]-path[k-1][1])*wb);
 const mapA=[],mapB=[],stations=256,total=arc.at(-1);let cursor=0;
 for(let k=0;k<=stations;k++){
  const at=total*k/stations;while(cursor<path.length-2&&arc[cursor+1]<at)cursor++;
  const t=(at-arc[cursor])/Math.max(1e-12,arc[cursor+1]-arc[cursor]),p=path[cursor],q=path[cursor+1];
  mapA.push(a.parameters[p[0]]*(1-t)+a.parameters[q[0]]*t);mapB.push(b.parameters[p[1]]*(1-t)+b.parameters[q[1]]*t);
 }
 // Symmetric averaging of monotone maps stays monotone. A short window
 // removes grid-step chatter while retaining the stationary inner axis.
 // A tiny uniform advance avoids repeated vertices at a stationary edge.
 // It changes parameter speed only, retaining the original contour exactly.
 const filtered=values=>values.map((v,k)=>{
  if(k===0)return 0;if(k===stations)return 1;let sum=0,weight=0;
  for(let j=-5;j<=5;j++){const w=6-Math.abs(j);sum+=w*values[Math.max(0,Math.min(stations,k+j))];weight+=w;}
  return .994*sum/weight+.006*k/stations;
 });
 const A=filtered(mapA),B=filtered(mapB);
 return {a:u=>curveA(monotone(A,u)),b:u=>curveB(monotone(B,u)),
  report:{method:'advancing points / interior chord / monotone arc correspondence',samples:count,pathSteps:path.length,mapA:A,mapB:B,objective:score.at(-1)}};
}
