import * as T from '../vendor/three.module.js';
import {sampleRailSection} from './yang-volume.js';

// Lifted movement belongs to the brush trajectory, not deposited material.
export function makePenTransfer(from,to){
 const p0=sampleRailSection(from.spec,1).a,p3=sampleRailSection(to.spec,0).a;
 const chord=p0.distanceTo(p3),out=p0.clone().sub(sampleRailSection(from.spec,.992).a).normalize(),
  into=sampleRailSection(to.spec,.008).a.sub(p3).normalize();
 const p1=p0.clone().addScaledVector(out,chord*.28),p2=p3.clone().addScaledVector(into,-chord*.22);
 p1.z+=chord*.10;p2.z+=chord*.10;
 const curve=new T.CubicBezierCurve3(p0,p1,p2,p3);
 return {from:from.stroke.role,to:to.stroke.role,start:from.stroke.end,end:to.stroke.start,
  curve,points:[p0,p1,p2,p3].map(p=>p.toArray()),geometryBridge:false,
  type:'lifted-return',scope:'Stroke 2 returns upward; the brush lifts across the visible gap and lands at stroke 3. The optional guide is not deposited material.'};
}
