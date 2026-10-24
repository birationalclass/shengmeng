import * as T from '../vendor/three.module.js';
import {sampleRailSection} from './yang-volume.js';
import {profile} from './stroke-volume.js';

// A continued brush gesture has one moving front, not two finished caps
// touching each other. Keep the relaxed four-rail scaffold of each piece,
// but sample it as one arclength domain and loft it with only two end poles.
export function continueBrushRun(parts){
 const first=parts[0],last=parts.at(-1),length=parts.reduce((n,p)=>n+p.spec.length,0),start=first.stroke.start,end=last.stroke.end;
 let offset=0;
 const runSegments=parts.map(part=>{const segment={spec:part.spec,stroke:part.stroke,from:offset/length,to:(offset+part.spec.length)/length};offset+=part.spec.length;return segment;});
 const timing=[];
 for(const segment of runSegments){
  const keys=segment.spec.gesture?.timing||[[0,0],[1,1]];
  // Give the return a duration proportional to its physical path length.
  // The former 0.09 s sub-stroke was only 2–3 frames at normal speed.
  for(const [t,u] of keys){const time=segment.from+t*(segment.to-segment.from),distance=segment.from+u*(segment.to-segment.from);if(timing.length&&Math.abs(timing.at(-1)[0]-time)<1e-10)continue;timing.push([time,distance]);}
 }
 const locate=u=>runSegments.find(segment=>u<segment.to)||runSegments.at(-1),joints=runSegments.slice(0,-1).map(segment=>segment.to);
 const raw=u=>{const segment=locate(u);return sampleRailSection(segment.spec,T.MathUtils.clamp((u-segment.from)/(segment.to-segment.from),0,1));};
 const runTransitions=joints.map(joint=>{
  const from=joint-.018,to=joint+.018,span=to-from,h=.0002,left=raw(from),right=raw(to),curves={};
  for(const edge of ['a','b']){const va=raw(from+h)[edge].sub(raw(from-h)[edge]).multiplyScalar(span/(6*h)),vb=raw(to+h)[edge].sub(raw(to-h)[edge]).multiplyScalar(span/(6*h));curves[edge]=new T.CubicBezierCurve3(left[edge],left[edge].clone().add(va),right[edge].clone().sub(vb),right[edge]);}
  return {from,to,...curves};
 });
 const control=field=>Array.from({length:129},(_,i)=>{
  const u=i/128,segment=locate(u),local=T.MathUtils.clamp((u-segment.from)/(segment.to-segment.from),0,1),original=profile(segment.spec.gesture?.[field]||(field==='pressure'?[1,1]:[0,0]),local);
  // Keep the returning face loaded across the turn. A separate stroke's
  // terminal pressure used to thin it before the next stroke restarted.
  const joint=joints.reduce((best,v)=>Math.abs(u-v)<Math.abs(u-best)?v:best,joints[0]),weight=1-T.MathUtils.smootherstep(Math.abs(u-joint),.018,.095);
  return field==='pressure'?T.MathUtils.lerp(original,Math.max(.88,original),weight):original+.16*Math.sin((u-joint)/.095*Math.PI)*weight;
 });
 const sections=[];
 for(const [index,segment] of runSegments.entries())for(let i=0;i<=segment.spec.count;i++){
  if(index&&i===0)continue;const q=segment.spec.sections[i],u=q.length/segment.spec.length,frame=sampleRailSection(segment.spec,u);
  sections.push({a:q.a.clone(),b:q.b.clone(),center:q.center.clone(),normal:frame.n,tangent:q.tangent.clone(),length:segment.from*length+q.length});
 }
 const sourceIndices=parts.flatMap(part=>part.sourceIndices),stroke={...first.stroke,name:first.stroke.name.replace(/内撇.*$/u,'长撇回锋 · 连入虫'),start,end,sourceIndices,continuousRun:true};
 const spec={...first.spec,start,end,sections,count:sections.length-1,length,runSegments,runTransitions,runPieceCount:parts.length,longitudinalScale:Math.max(1,.75*parts.length),
  stitchStart:!!first.spec.stitchStart,stitchEnd:!!last.spec.stitchEnd,forceReveal:false,
  gesture:{anchor:'a',continuous:true,turns:joints,wake:.055,timing,pressure:control('pressure'),roll:control('roll'),
   phases:[[0,'承势落锋'],[joints[0]*.25,'按行长撇'],[Math.max(0,joints[0]-.085),'回锋不断'],[joints[0],'翻面入虫'],[.96,'提锋收束']]}};
 return {stroke,kind:'rail',spec,sourceIndices,run:{sourceIndices,start,end,length,joints,timing,mesh:'one closed loft; only start/end poles; no internal cap'}};
}

export function combineContinuousRuns(parts){
 const result=[];
 for(let i=0;i<parts.length;i++){
  const group=[parts[i]];
  while(i+1<parts.length&&parts[i+1].stroke.continuousFrom&&parts[i+1].stroke.continuousFrom===group.at(-1).stroke.role&&(parts[i+1].stroke.character||0)===(group[0].stroke.character||0))group.push(parts[++i]);
  result.push(group.length>1?continueBrushRun(group):group[0]);
 }
 return result;
}
