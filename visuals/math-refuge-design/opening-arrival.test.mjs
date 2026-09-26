import test from 'node:test';
import assert from 'node:assert/strict';
import {openingArrivalProfile} from './opening-arrival.js';
test('arrival has continuous distance and speed, non-stop door crossing, and stops at second row',()=>{
 const inside=2.9*Math.SQRT2,p=openingArrivalProfile(3000,inside),eps=1e-5;
 for(const t of [p.flightSeconds,p.doorTime,p.duration]){
  const a=p.sample(t-eps),b=p.sample(t+eps);assert(Math.abs(a.distance-b.distance)<.001);assert(Math.abs(a.speed-b.speed)<.001);
 }
 assert.equal(p.sample(p.doorTime).speed,1.2);assert.equal(p.sample(p.duration).speed,0);
 assert(Math.abs(p.sample(p.duration).distance-3000-10.8-inside)<1e-8);
 let last=Infinity;
 for(let t=p.flightSeconds;t<=p.duration;t+=.02){const s=p.sample(t);assert(s.speed<=last+1e-8);assert(s.speed>=0);last=s.speed;}
 for(let t=0;t<p.duration;t+=.1)assert(p.sample(t).speed>=0);
});

import * as T from '../3d/vendor/three.module.js';
import {createOpeningRoute} from './opening-arrival.js';
test('3D arrival path joins the doorway straight without a tangent or curvature kink',()=>{
 const end=new T.Vector3(38.4,2.096,0),route=createOpeningRoute(T,new T.Vector3(-2944,446,0),end),h=.00001;
 assert(route.getPoint(1).distanceTo(end)<1e-10);
 const last=route.getPoint(1).sub(route.getPoint(1-h)).normalize();assert(last.distanceTo(new T.Vector3(1,0,0))<1e-6);
 const a=route.getTangent(1-h),b=route.getTangent(1-2*h);assert(a.distanceTo(b)<1e-6);
});

test('opening reaches the hall promptly without shortening the final doorway brake',()=>{
 const p=openingArrivalProfile(3016.34,2.9*Math.SQRT2);
 assert(p.doorTime<18.2);assert(p.doorTime>17.5);
 assert.equal(p.doorTime-p.flightSeconds,3);
 assert.equal(p.sample(p.doorTime).speed,1.2);
});
