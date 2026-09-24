import test from 'node:test';import assert from 'node:assert/strict';
import {apparentAltitude,refractionDegrees} from './solar-optics.js';
import {advanceWeatherWinds,windVelocity} from './cloud-wind.js';
import {hallFloorRoute,slabHit,stopAtHallSlab,HALL_SLAB} from './hall-camera-route.js';
import * as T from '../3d/vendor/three.module.js';
test('near-horizon refraction lifts and compresses the solar limb continuously',()=>{
 assert(refractionDegrees(0)>.5&&refractionDegrees(0)<.65);
 const r=.266,low=apparentAltitude(-r),high=apparentAltitude(r);
 assert(high-low<2*r&&high-low>.7*2*r);
 assert(apparentAltitude(20)-20<.06);
 let prev=apparentAltitude(-3);for(let h=-2.999;h<12;h+=.001){const v=apparentAltitude(h);assert(v>prev&&v-prev<.002);prev=v;}
});
test('independent water wind never acquires the solar clock playback multiplier',()=>{
 const water=()=>({velocity:windVelocity(12,90),offset:{x:0,z:0}}),a=water(),b=water(),c=water(),d=water();
 for(let i=0;i<600;i++){advanceWeatherWinds(c,a,12,90,1/60,1);advanceWeatherWinds(d,b,12,90,1/60,60);}
 assert.deepEqual(a,b);assert(Math.abs(d.offset.x/c.offset.x-60)<1e-8);assert(Math.abs(a.offset.x+12/3600*10)<1e-10);
});
test('two-way hall transitions use exterior stair route without intersecting the slab',()=>{
 const high=[53,7.62,6.9],low=[50,2.1,0];
 for(const [a,b] of [[high,low],[low,high]]){
  const route=hallFloorRoute(a,b);assert(route);
  const curve=new T.CatmullRomCurve3(route.map(p=>new T.Vector3(...p)),false,'centripetal');let prior=curve.getPointAt(0).toArray();
  for(let i=1;i<=1000;i++){const next=curve.getPointAt(i/1000).toArray();assert.equal(slabHit(prior,next),null,'route crosses slab');prior=next;}
 }
 const stopped=stopAtHallSlab(high,low);assert(stopped[1]>HALL_SLAB.max[1]);
 assert.equal(hallFloorRoute([80,10,0],[80,2,0]),null);
});
import {cameraProbeRadius,HallPassageMask,curveClearsHall} from './hall-camera-route.js';
test('near-plane probe grows with FOV and aspect ratio',()=>{assert(cameraProbeRadius(.1,90,2)>cameraProbeRadius(.1,45,1));});
test('manual slab passage is masked in both directions and recovers without moving endpoints',()=>{
 const high=[53,7.62,6.9],low=[50,2.1,0];
 for(const [a,b] of [[high,low],[low,high]]){const mask=new HallPassageMask(),copy=[...b];assert.equal(mask.update(a,b,.2,.016),1);assert.deepEqual(b,copy);for(let i=0;i<60;i++)mask.update(b,b,.2,1/60);assert.equal(mask.opacity,0);}
 const mask=new HallPassageMask();assert.equal(mask.update([80,10,0],[80,2,0],.2,.016),0);
});
test('route validator rejects curves that sweep through the slab',()=>{const c=new T.LineCurve3(new T.Vector3(53,7.62,6.9),new T.Vector3(50,2.1,0));assert.equal(curveClearsHall(c),false);});
