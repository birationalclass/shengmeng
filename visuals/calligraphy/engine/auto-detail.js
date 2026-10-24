import * as T from '../vendor/three.module.js';
import {profile} from './stroke-volume.js';

const brush={
 dot:{front:[.3,.55,.68,.5,.19],back:[.22,.39,.44,.31,.13],pressure:[.75,1.06,1.13,.86,.5],depth:[-.15,.1,.35,.18,-.08],bank:[-.3,.25,-.15],caps:[.12,.16]},
 cross:{front:[.24,.44,.49,.39,.24],back:[.18,.3,.32,.25,.17],pressure:[.88,1.06,1,.92,.8],depth:[-.2,.05,.33,.12,-.15],bank:[-.2,.23,-.18],caps:[.035,.045]},
 down:{front:[.3,.49,.55,.42,.24],back:[.23,.33,.37,.29,.17],pressure:[.88,1.07,1,.91,.72],depth:[.15,.39,.26,-.05,-.3],bank:[.22,-.23,.2],caps:[.035,.055]},
 left:{front:[.26,.49,.56,.34,.15],back:[.19,.31,.35,.23,.1],pressure:[.9,1.07,1.02,.9,.55],depth:[.13,.4,.21,-.14,-.34],bank:[-.25,.32,-.22],caps:[.035,.11]},
 turn:{front:[.3,.43,.59,.46,.23],back:[.22,.3,.36,.28,.15],pressure:[.9,1.06,.88,1,.65],depth:[-.15,.11,.4,.12,-.32],bank:[-.28,.38,-.3,.16],caps:[.035,.065]},
 sweep:{front:[.23,.42,.57,.62,.18],back:[.17,.27,.36,.37,.11],pressure:[.8,.94,1.08,1.12,.52],depth:[-.2,.1,.39,.22,-.27],bank:[-.23,.33,-.25],caps:[.045,.12]}
};
const cross=(a,b)=>a[0]*b[1]-a[1]*b[0];
function interval(point,normal,polygons){
 const hits=[];
 for(const polygon of polygons)for(let i=1;i<polygon.length;i++){
  const a=polygon[i-1],b=polygon[i],edge=[b[0]-a[0],b[1]-a[1]],rel=[a[0]-point[0],a[1]-point[1]],den=cross(normal,edge);if(Math.abs(den)<1e-9)continue;
  const t=cross(rel,edge)/den,v=cross(rel,normal)/den;if(v>=-.000001&&v<=1.000001)hits.push(t);
 }
 const negative=hits.filter(v=>v<=0).sort((a,b)=>b-a),positive=hits.filter(v=>v>0).sort((a,b)=>a-b);
 if(negative.length&&positive.length)return [negative[0],positive[0]];
 hits.sort((a,b)=>a-b);let best=null,distance=Infinity;
 for(let i=0;i+1<hits.length;i+=2){const d=Math.abs((hits[i]+hits[i+1])/2);if(d<distance){distance=d;best=[hits[i],hits[i+1]];}}
 return best||[-7,7];
}
function smooth(values){const filtered=values.map((v,i)=>[values[Math.max(0,i-1)],v,values[Math.min(values.length-1,i+1)]].sort((a,b)=>a-b)[1]);return filtered.map((v,i)=>(filtered[Math.max(0,i-1)]+2*v+filtered[Math.min(values.length-1,i+1)])/4);}
function roundedMedian(median,polygon){
 let points=median.map(([x,y])=>new T.Vector3(x,y,0));
 // Remove redundant short collinear intervals before constructing round turns.
 for(let pass=0;pass<2;pass++)points=points.filter((p,i)=>{if(!i||i===points.length-1)return true;const a=p.clone().sub(points[i-1]),b=points[i+1].clone().sub(p);return a.clone().normalize().angleTo(b.clone().normalize())>.13||a.length()+b.length()>points[i+1].distanceTo(points[i-1])+3;});
 const result=[points[0]];
 for(let i=1;i<points.length-1;i++){
  const p=points[i],incoming=p.clone().sub(points[i-1]),outgoing=points[i+1].clone().sub(p),angle=incoming.angleTo(outgoing);if(angle<.28){result.push(p);continue;}
  const direction=points[i+1].clone().sub(points[i-1]).normalize(),[lo,hi]=interval([p.x,p.y],[-direction.y,direction.x],polygon),cut=Math.min(incoming.length()*.3,outgoing.length()*.3,Math.max(8,Math.min(75,(hi-lo)*.8)));
  const a=p.clone().addScaledVector(incoming.normalize(),-cut),b=p.clone().addScaledVector(outgoing.normalize(),cut);result.push(a);
  for(let j=1;j<=5;j++){const t=j/5,q=1-t;result.push(a.clone().multiplyScalar(q*q).addScaledVector(p,2*q*t).addScaledVector(b,t*t));}
 }
 result.push(points.at(-1));return result.filter((p,i)=>!i||p.distanceTo(result[i-1])>.001);
}
function family(curve){
 const start=curve.getPoint(0),end=curve.getPoint(1),box=new T.Box3().setFromPoints(curve.getPoints(40)),size=box.getSize(new T.Vector3()),length=curve.getLength(),dx=end.x-start.x,dy=end.y-start.y;let turning=0;
 for(let i=1;i<=20;i++)turning+=curve.getTangentAt((i-1)/20).angleTo(curve.getTangentAt(i/20));
 if(length<165&&Math.max(size.x,size.y)/Math.max(10,Math.min(size.x,size.y))<2.7)return 'dot';
 if(turning>1.0)return 'turn';if(Math.abs(dx)>Math.abs(dy)*2)return 'cross';if(Math.abs(dy)>Math.abs(dx)*2)return 'down';return dx<0||dy>0?'left':'sweep';
}
function gestureMotion(sections,kind){
 const elapsed=[0];let total=0;
 for(let i=1;i<sections.length;i++){const turn=sections[i].tangent.angleTo(sections[i-1].tangent);total+=1+(kind==='turn'?2.1:1.2)*Math.min(1,turn*5);elapsed.push(total);}
 const values=[0];let j=1;
 for(let k=1;k<8;k++){const target=k/8*total;while(j<elapsed.length-1&&elapsed[j]<target)j++;const u=(j-1+(target-elapsed[j-1])/Math.max(1e-9,elapsed[j]-elapsed[j-1]))/(sections.length-1);values.push(u);}values.push(1);return values;
}
export function sculptAutomaticGlyph(char,data,polygons){
 const strokes=data.medians.map((median,index)=>{
  if(median.length<2)throw Error(`「${char}」的笔画数据不完整。`);
  const curve=new T.CatmullRomCurve3(roundedMedian(median,polygons[index]),false,'centripetal');curve.arcLengthDivisions=1200;
  const type=family(curve),design=brush[type],count=T.MathUtils.clamp(Math.ceil(curve.getLength()/17),16,64),sections=[];
  for(let i=0;i<=count;i++){
   const u=i/count,p=curve.getPointAt(u),tangent=curve.getTangentAt(T.MathUtils.clamp(u,.0001,.9999)).normalize(),normal=[-tangent.y,tangent.x],[lo,hi]=interval([p.x,p.y],normal,polygons[index]);
   const width=T.MathUtils.clamp(hi-lo,5,180);sections.push({u,p,tangent,normal,width,shift:T.MathUtils.clamp((lo+hi)/2,-width*.28,width*.28)});
  }
  const widths=smooth(sections.map(s=>s.width)),shifts=smooth(sections.map(s=>s.shift)),a=[],b=[],depthLo=Math.min(...design.depth),depthHi=Math.max(...design.depth),depthMid=(depthLo+depthHi)/2,depthScale=Math.min(1,curve.getLength()*.0037*.45/(depthHi-depthLo));let previousAngle=Math.atan2(sections[0].tangent.y,sections[0].tangent.x),angle=previousAngle,startAngle=angle;
  sections.forEach((section,i)=>{
   const {u,p,normal,tangent}=section,heading=Math.atan2(tangent.y,tangent.x);let delta=heading-previousAngle;while(delta>Math.PI)delta-=Math.PI*2;while(delta<-Math.PI)delta+=Math.PI*2;angle+=delta;previousAngle=heading;
   const bank=profile(design.bank,u)+T.MathUtils.clamp((angle-startAngle)*.18,-.3,.3),z=depthMid+(profile(design.depth,u)-depthMid)*depthScale+(((index*7)%5)-2)*.065,width=widths[i]*profile(design.pressure,u);
   const P=side=>{const distance=shifts[i]+side*width*.5;return [(p.x+normal[0]*distance*Math.cos(bank)-512)*.0037,(p.y+normal[1]*distance*Math.cos(bank)-420)*.0037,z+distance*.0037*Math.sin(bank)];};a.push(P(-1));b.push(P(1));
  });
  return {name:`${char} · ${index+1}`,a,b,front:design.front,back:design.back,crown:type==='turn'?[.42,.65,.5,.43]:[.45,.59,.54,.46],rearCrown:[.5,.44,.52],camber:type==='turn'?[0,.045,.01,0]:[0,.025,0],capStart:design.caps[0],capEnd:design.caps[1],safeBend:true,detail:{level:'procedural',family:type,version:2},motion:gestureMotion(sections,type),weight:.2+Math.sqrt(curve.getLength())/20};
 });
 const end=Math.min(4.3,1.5+strokes.length*.085),gap=.018,available=end-.06-gap*(strokes.length-1),sum=strokes.reduce((n,s)=>n+s.weight,0);let clock=.06;
 for(const s of strokes){s.start=clock;s.end=clock+available*s.weight/sum;clock=s.end+gap;delete s.weight;}
 return {id:'data:'+char,text:char,title:'自动塑形',subtitle:'分类提按，过弯收锋',kind:'rail',detailLevel:'procedural',strokes,writeStart:.06,writeEnd:end,frontalAt:end+1.45,duration:Math.max(6,Math.ceil(end+2.8)),requiresLicense:true,
  source:{name:char+' · 通用自动造型',phrase:'分类截面、转角收锋与空间笔势',url:'https://github.com/chanind/hanzi-writer-data',image:'',caption:'自动构形，未经逐笔人工精修',description:'字形轮廓和笔顺来自本地 Hanzi Writer Data 2.0.1。按点、横、竖、撇、捺、折分别控制提按、截面和深度，并在紧弯处收窄截面以减少挤皱。仍属程序造型，不等同于逐笔人工设计或书家原帖。'}};
}
