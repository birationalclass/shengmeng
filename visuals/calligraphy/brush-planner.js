import * as T from './vendor/three.module.js';
import {sampleRailSection} from './engine/yang-volume.js';
import {profile} from './engine/stroke-volume.js';

// Infer motion from the existing surface. These controls are estimates, not
// recovered calligrapher motion, and do not replace the source character shape.
const clamp=T.MathUtils.clamp,N=64,KEYS=21;
const signedAngle=(a,b)=>Math.atan2(Math.sin(b-a),Math.cos(b-a));
const field=(values,u)=>{const x=clamp(u,0,1)*(values.length-1),i=Math.min(values.length-2,Math.floor(x));return T.MathUtils.lerp(values[i],values[i+1],x-i);};
const blur=values=>values.map((_,i)=>[-2,-1,0,1,2].reduce((sum,d)=>sum+values[clamp(i+d,0,values.length-1)]*(3-Math.abs(d)),0)/9);
const compact=values=>Array.from({length:KEYS},(_,i)=>field(values,i/(KEYS-1)));

function measure(part){
 const sections=Array.from({length:N+1},(_,i)=>sampleRailSection(part.spec,i/N));
 const headings=sections.map((_,i)=>{
  const a=sections[Math.max(0,i-1)].center,b=sections[Math.min(N,i+1)].center;
  return Math.atan2(b.y-a.y,b.x-a.x);
 });
 const curvature=blur(headings.map((_,i)=>signedAngle(headings[Math.max(0,i-2)],headings[Math.min(N,i+2)])));
 const maxWidth=Math.max(...sections.map(q=>q.width),1e-6);
 return {sections,headings,curvature,maxWidth};
}

function inferGesture(part,m){
 if(part.spec.length<1e-7)return null;
 const dot=part.spec.dotRefined||part.stroke.detail?.family==='dot'||part.spec.length<m.maxWidth*1.6;
 const pressure=[],roll=[],spread=[],elapsed=[0];
 let corner=0,cornerWeight=0;
 for(let i=0;i<=N;i++){
  const u=i/N,w=clamp(m.sections[i].width/m.maxWidth,0,1),turn=clamp(m.curvature[i]*2.6,-1,1);
  const entry=T.MathUtils.smootherstep(u,0,.10),exit=1-T.MathUtils.smootherstep(u,.82,1);
  pressure.push(clamp((dot?.70+.44*Math.sin(Math.PI*u):.64+.43*Math.sqrt(w)-.16*Math.abs(turn))*(.62+.38*entry)*(.60+.40*exit),.35,1.14));
  roll.push((dot?.075:.24)*turn*Math.sin(Math.PI*u));
  spread.push(dot?.30+.42*Math.sin(Math.PI*u):clamp(.10+.11*Math.sqrt(w)+.09*Math.abs(turn),.10,.34));
  if(u>.13&&u<.85&&Math.abs(turn)>cornerWeight){corner=u;cornerWeight=Math.abs(turn);}
  if(i){const distance=m.sections[i].center.distanceTo(m.sections[i-1].center);
   const load=.62+.42*Math.sqrt(w)+.85*Math.abs(turn)+.72*Math.exp(-.5*((u-.055)/.045)**2)+.45*Math.exp(-.5*((u-.95)/.045)**2);
   elapsed.push(elapsed.at(-1)+Math.max(distance,1e-8)*load);
  }
 }
 const timing=[[0,0]];let at=1;
 for(let k=1;k<12;k++){
  const t=k/12,target=elapsed.at(-1)*t;while(at<N&&elapsed[at]<target)at++;
  const inferred=(at-1+(target-elapsed[at-1])/Math.max(1e-9,elapsed[at]-elapsed[at-1]))/N;
  const u=clamp(.60*inferred+.40*profile(part.spec.motion||[0,1],t),timing.at(-1)[1]+1e-5,1-(12-k)*1e-5);
  timing.push([t,u]);
 }
 timing.push([1,1]);
 const phases=[[0,'入笔蓄势'],[.12,dot?'按笔成点':'按笔铺锋']];
 if(cornerWeight>.18)phases.push([clamp(corner-.035,.17,.80),'提锋转向']);
 phases.push([.85,'提锋收束'],[.97,'离笔承势']);phases.sort((a,b)=>a[0]-b[0]);
 return {inferred:true,revision:'geometry-brush-plan-v1',anchor:dot?'center':'a',wake:dot?.16:clamp(m.maxWidth/part.spec.length*.75,.045,.16),
  timing,pressure:compact(pressure),roll:compact(roll),tipSpread:compact(spread),leadingEdge:0,phases};
}

export function applyBrushPlan(parts){
 const groups=new Map();
 for(const part of parts){const id=part.stroke.character||0;if(!groups.has(id))groups.set(id,[]);groups.get(id).push(part);}
 const report={revision:'geometry-brush-plan-v1',authoredStrokes:0,inferredStrokes:0,lifts:[],retimedCharacters:[],
  scope:'Motion estimated from width, curvature and stroke spacing. Lifted moves deposit no connector. The final character shape is unchanged.'};
 for(const [id,group] of groups){
  const hasWind=group.some(p=>p.stroke.role?.startsWith('wind-'));
  if(hasWind){report.authoredStrokes+=group.filter(p=>p.spec.gesture).length;continue;}
  for(const part of group){
   if(part.spec.gesture){report.authoredStrokes++;continue;}
   const m=measure(part),gesture=inferGesture(part,m);
   if(gesture){part.spec.gesture=gesture;report.inferredStrokes++;}
  }
  const box=new T.Box3();for(const part of group)for(const q of part.spec.sections)box.expandByPoint(q.center);
  const size=box.getSize(new T.Vector3()),span=Math.max(.01,Math.hypot(size.x,size.y)),gaps=[0],moves=[];
  for(let i=1;i<group.length;i++){
   const previous=group[i-1],current=group[i],a=sampleRailSection(previous.spec,.99),end=sampleRailSection(previous.spec,1),start=sampleRailSection(current.spec,0),b=sampleRailSection(current.spec,.01);
   const distance=end.center.distanceTo(start.center),out=Math.atan2(end.center.y-a.center.y,end.center.x-a.center.x),into=Math.atan2(b.center.y-start.center.y,b.center.x-start.center.x),angle=signedAngle(out,into);
   gaps.push(clamp(.027+.040*Math.sqrt(distance/span)+.018*Math.abs(angle)/Math.PI,.027,.095));
   moves.push({previous,current,distance,turn:angle});
   if(current.spec.gesture?.inferred){const g=current.spec.gesture,incoming=Math.atan2(start.center.y-end.center.y,start.center.x-end.center.x),entry=.14*Math.sin(signedAngle(incoming,into));
    g.roll=g.roll.map((value,k)=>value+entry*(1-T.MathUtils.smootherstep(k/(g.roll.length-1),0,.18)));
   }
  }
  // Existing authored timing and constrained continuous strokes stay intact.
  // Automatic glyphs get distance-aware lifts within their original duration.
  if(group.every(p=>p.stroke.detail?.level==='procedural'&&!p.stroke.connection&&!p.stroke.continuousFrom&&!p.stroke.joinFrom)){
   const start=group[0].stroke.start,end=group.at(-1).stroke.end,total=end-start,sumGaps=gaps.reduce((a,b)=>a+b,0),gapScale=Math.min(1,total*.22/Math.max(1e-8,sumGaps));
   const weights=group.map(p=>Math.max(.001,p.stroke.end-p.stroke.start)),sumWeights=weights.reduce((a,b)=>a+b,0),body=total-sumGaps*gapScale;let time=start;
   group.forEach((part,i)=>{time+=gaps[i]*gapScale;const finish=i===group.length-1?end:time+body*weights[i]/sumWeights;part.stroke={...part.stroke,start:time,end:finish};time=finish;});
   report.retimedCharacters.push(id);
  }
  for(const {previous,current,distance,turn} of moves)if(current.spec.gesture?.inferred){
   report.lifts.push({from:previous.sourceIndices.at(-1),to:current.sourceIndices[0],start:previous.stroke.end,end:current.stroke.start,distance,turn,depositsInk:false});
  }
 }
 return report;
}
