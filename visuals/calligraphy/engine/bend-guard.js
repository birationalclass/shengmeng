import {profile} from './stroke-volume.js';

// A swept section wider than its local bend radius folds through itself.
// Lift the brush through those turns by reducing the local section smoothly.
// This is a local curvature guard, not a global self-intersection solver.
export function guardRailBends(spec){
 if(!spec.safeBend)return spec;
 const original=spec.sections.map(section=>({a:section.a.clone(),b:section.b.clone()}));
 let minScale=1;
 for(let i=0;i<=spec.count;i++){
  const current=spec.sections[i],before=spec.sections[Math.max(0,i-2)],after=spec.sections[Math.min(spec.count,i+2)];
  const angle=Math.acos(Math.max(-1,Math.min(1,before.tangent.dot(after.tangent))));
  if(angle<1e-7)continue;
  const radius=before.center.distanceTo(after.center)/angle;
  const delta=original[i].b.clone().sub(original[i].a);delta.addScaledVector(current.tangent,-delta.dot(current.tangent));
  const u=i/spec.count,r=delta.length()*Math.max(.5,profile(spec.front,u),profile(spec.back,u));
  const ratio=r/Math.max(1e-7,.8*radius),scale=Math.pow(1+Math.pow(ratio,6),-1/6);
  current.a.copy(current.center).addScaledVector(delta,-.5*scale);current.b.copy(current.center).addScaledVector(delta,.5*scale);minScale=Math.min(minScale,scale);
 }
 spec.bendGuard={minScale,method:'local curvature / smooth section reduction'};return spec;
}
