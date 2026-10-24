import * as T from '../vendor/three.module.js';
import {sampleRailSection} from './yang-volume.js';
import {profile} from './stroke-volume.js';

const smooth=t=>{t=T.MathUtils.clamp(t,0,1);return t*t*t*(10+t*(-15+6*t));};
const mix=T.MathUtils.lerp;
const bezier=(a,b,c,d,t)=>a.clone().multiplyScalar((1-t)**3).addScaledVector(b,3*t*(1-t)**2).addScaledVector(c,3*t*t*(1-t)).addScaledVector(d,t**3);
const tangent=(a,b,c,d,t)=>b.clone().sub(a).multiplyScalar(3*(1-t)**2).addScaledVector(c.clone().sub(b),6*(1-t)*t).addScaledVector(d.clone().sub(c),3*t*t).normalize();

// Prepend the lifted return to stroke 3, joining its existing pressed body.
// Endpoints come from the ACTUAL relaxed sections, so the link also follows
// text placement, depth/fullness changes and overlap adjustments.
export function attachStrokeLink(body,previous){
 const attach=.035,end=sampleRailSection(body,attach),start=sampleRailSection(previous,1),near=sampleRailSection(previous,.992);
 const p0=start.center.clone(),p3=end.center.clone(),out=previous.sections.at(-1).tangent.clone().normalize();
 const inDirection=body.sections[Math.min(body.count,Math.round(attach*body.count))].tangent.clone();
 // The body is sampled by arclength, while its section array uses the raw
 // spline parameter. Obtain the incoming tangent from neighboring arc samples.
 inDirection.copy(sampleRailSection(body,attach+.001).center).sub(sampleRailSection(body,attach-.001).center).normalize();
 const chord=p0.distanceTo(p3),p1=p0.clone().addScaledVector(out,chord*.24),p2=p3.clone().addScaledVector(inDirection,-chord*.17);
 const N=200,M=600,points=Array.from({length:N+1},(_,i)=>bezier(p0,p1,p2,p3,i/N)),directions=Array.from({length:N+1},(_,i)=>tangent(p0,p1,p2,p3,i/N));
 let axis=near.d.clone().addScaledVector(out,-near.d.dot(out));if(axis.lengthSq()<1e-6)axis.set(1,0,0).addScaledVector(out,-out.x);axis.normalize();
 const axes=[axis.clone()];
 for(let i=1;i<=N;i++){axis=axis.clone().applyQuaternion(new T.Quaternion().setFromUnitVectors(directions[i-1],directions[i])).normalize();axes.push(axis);}
 const finalAxis=axes.at(-1),twist=Math.atan2(inDirection.dot(finalAxis.clone().cross(end.d)),finalAxis.dot(end.d));
 const hairline=Math.min(.020,previous.length*.0033),sections=[],fields=[],keys=['front','back','crown','rearCrown','camber','sectionPower'];
 const endRatios={front:end.front/Math.max(end.width,1e-8),back:end.back/Math.max(end.width,1e-8),crown:end.crown,rearCrown:end.rear,camber:end.camber/Math.max(end.width,1e-8),sectionPower:profile(body.sectionPower||[2.4,2.4],attach)};
 const later=sampleRailSection(body,attach+.004),bodyWidthSlope=(later.width-end.width)/Math.max(1e-8,later.center.distanceTo(end.center));
 function push(center,direction,across,width,field){
  const normal=new T.Vector3().crossVectors(direction,across).normalize(),a=center.clone().addScaledVector(across,-width*.5),b=center.clone().addScaledVector(across,width*.5);
  const length=sections.length?sections.at(-1).length+sections.at(-1).center.distanceTo(center):0;
  sections.push({center,a,b,tangent:direction,normal,length});fields.push(field);
 }
 for(let i=0;i<N;i++){
  const t=i/N,direction=directions[i],across=axes[i].clone().applyAxisAngle(direction,twist*smooth(t)),blend=smooth((t-.70)/.30);
  const entry=Math.min(1,t/.008);
  let width=hairline*Math.sqrt(Math.max(0,1-(1-entry)**2));
  if(t>.70){
   const u=(t-.70)/.30,h=u*u,k=h*u,slope=T.MathUtils.clamp(bodyWidthSlope*3*p3.distanceTo(p2)*.30,0,Math.max(0,3*(end.width-hairline)));
   width=(2*k-3*h+1)*hairline+(-2*k+3*h)*end.width+(k-h)*slope;
  }
  push(points[i],direction,across,width,{front:mix(.44,endRatios.front,blend),back:mix(.32,endRatios.back,blend),crown:mix(.5,endRatios.crown,blend),rearCrown:mix(.5,endRatios.rearCrown,blend),camber:mix(0,endRatios.camber,blend),sectionPower:mix(2.15,endRatios.sectionPower,blend)});
 }
 const joinIndex=sections.length;
 for(let i=0;i<=M;i++){
  const u=attach+(1-attach)*i/M,q=sampleRailSection(body,u),direction=sampleRailSection(body,Math.min(1,u+.0001)).center.sub(sampleRailSection(body,Math.max(0,u-.0001)).center).normalize();
  push(q.center,direction,q.d,q.width,{front:q.front/Math.max(q.width,1e-8),back:q.back/Math.max(q.width,1e-8),crown:q.crown,rearCrown:q.rear,camber:q.camber/Math.max(q.width,1e-8),sectionPower:profile(body.sectionPower||[2.4,2.4],u)});
 }
 const length=sections.at(-1).length,joinDistance=sections[joinIndex].length,fraction=joinDistance/length,profiles=Object.fromEntries(keys.map(key=>[key,[]]));let cursor=0;
 for(let i=0;i<=160;i++){
  const at=length*i/160;while(cursor<sections.length-2&&sections[cursor+1].length<at)cursor++;
  const u=T.MathUtils.clamp((at-sections[cursor].length)/Math.max(1e-9,sections[cursor+1].length-sections[cursor].length),0,1);
  for(const key of keys)profiles[key].push(mix(fields[cursor][key],fields[cursor+1][key],u));
 }
 const previousKeys=previous.gesture.timing,last=previousKeys.at(-1),beforeLast=previousKeys.at(-2),outgoingSpeed=previous.length*(last[1]-beforeLast[1])/(last[0]-beforeLast[0])/(previous.end-previous.start);
 const incomingSlope=outgoingSpeed*(body.end-body.start)/length,firstDistance=incomingSlope*.08;
 const gesture={...body.gesture,wake:.065,leadingEdge:-.12,
  timing:[[0,0],[.08,firstDistance],[.25,.78*fraction],[.36,fraction],[.47,fraction+.08*(1-fraction)],[.70,fraction+.70*(1-fraction)],[.90,fraction+.96*(1-fraction)],[1,1]],
  phases:[[0,'二→三 · 牵丝回带'],[fraction*.84,'转锋落笔'],[fraction+.08*(1-fraction),'第三笔行锋'],[.94,'提锋接势']]};
 return {...body,...profiles,sections,count:sections.length-1,length,capStart:0,capEnd:0,safeBend:false,brush:'linked-lens-v1',surfaceStyle:'lens',gesture,
  link:{from:'wind-main',to:'wind-inner',start:p0.toArray(),end:p3.toArray(),controls:[p0,p1,p2,p3].map(p=>p.toArray()),fraction,joinIndex,hairline,endpointGap:start.center.distanceTo(sections[0].center),tangentAngle:out.angleTo(directions[0]),outgoingSpeed,incomingSpeed:length*incomingSlope/(body.end-body.start)},joinable:true};
}
