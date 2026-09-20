import * as T from '../3d/vendor/three.module.js';
import {jointMotion} from './architectural-motion.mjs?v=living1';
// One pitch module throughout: tangential velocities match at every contact.
export const GEAR_TEETH=[28,20,28,32,24];
export function gearTrain(){let x=0;const gears=GEAR_TEETH.map((teeth,i)=>{const radius=teeth*.035;if(i)x+=(GEAR_TEETH[i-1]+teeth)*.035;return {teeth,radius,x,speed:.36*28/teeth*(i%2?-1:1)};});const center=(gears[0].x+gears.at(-1).x)/2;return gears.map(g=>({...g,x:g.x-center}));}
export function clockworkCity(a,p){
 const M=a.materials,g=new T.Group();p.add(g);g.userData.domain='precision-clockwork';
 const steel=new T.MeshStandardMaterial({color:0x40535d,roughness:.35,metalness:.8}),warm=new T.MeshStandardMaterial({color:0xffd58c,emissive:0xc87e27,emissiveIntensity:.55});
 // Freestanding skeleton: the gear train remains exposed from the playing view.
 a.box(g,[10,.3,3],[0,.25,-8.4],M.stone);
 for(const x of [-5,5]){a.box(g,[.24,4.9,.30],[x,2.65,-8.65],steel);for(let j=0;j<3;j++)a.box(g,[.65,.16,.68],[x,.5+j*1.65,-8.65],M.brass);}
 for(const y of [.8,4.9])a.box(g,[10.4,.18,.30],[0,y,-8.65],steel);
 a.rod(g,[-5,.7,-8.8],[0,4.9,-8.8],.065,M.brass);a.rod(g,[0,4.9,-8.8],[5,.7,-8.8],.065,M.brass);
 const face=new T.Group();g.add(face);face.position.set(0,2.95,-8.05);face.rotation.x=Math.PI/2;
 for(const [i,spec]of gearTrain().entries()){
  // Tooth tips extend beyond the pitch circle; alternating angular phases mesh.
  const wheel=a.gear(face,spec.radius*1.035,spec.teeth,[spec.x,0,0],spec.speed,M.brass);wheel.userData.gearTrain=spec;wheel.userData.phase=i%2?Math.PI/spec.teeth:0;
  a.cylinder(face,.11,.5,[spec.x,.16,0],steel);a.cylinder(face,.19,.06,[spec.x,.44,0],M.gold);
 }
 // Secondary reducer in a parallel plane, linked by the central spindle.
 for(const [x,r,teeth,speed]of [[-.14,.49,16,-.36*28/16],[1.33,.98,32,.36*28/32]]){a.gear(face,r,teeth,[x,-.23,-1.65],speed,steel);a.cylinder(face,.09,.7,[x,0,-1.65],M.gold);}
 // Pierced copper belfries frame the exposed mechanism, rather than hiding it.
 for(const side of [-1,1]){const tower=new T.Group();g.add(tower);tower.position.set(side*5.75,.15,-8.7);
  a.cylinder(tower,.91,.25,[0,.15,0],M.stone);a.cylinder(tower,.73,3.8,[0,2.08,0],M.stone);
  for(const y of [.6,1.65,2.75,4.05])a.cylinder(tower,.80,.12,[0,y,0],M.brass);
  for(const xx of [-.36,.36])a.box(tower,[.16,.85,.05],[xx,2.7,.69],warm);
  for(let k=0;k<6;k++){const angle=k*Math.PI/3;a.cylinder(tower,.05,1.25,[Math.sin(angle)*.69,4.64,Math.cos(angle)*.69],M.brass);}
  a.cylinder(tower,.85,.13,[0,5.28,0],M.brass);a.mesh(tower,new T.ConeGeometry(1.05,1.35,8),steel,[0,5.98,0]);a.rod(tower,[0,6.65,0],[0,7.12,0],.035,M.gold);
  const bell=a.mesh(tower,new T.CylinderGeometry(.19,.42,.65,16),M.gold,[0,4.58,0]);jointMotion(a,bell,{axis:'z',speed:.72,amplitude:.08,phase:side});
 }
 // Twin screw towers and articulated walking beams transfer rotation to the lift.
 a.clockworkLifts=[];
 for(const side of [-1,1]){
  const x=side*8.15,z=-1.15;
  a.box(g,[2.45,.3,5.3],[x,.3,z],M.stone);
  for(const zz of [-2.85,.55])for(const dx of [-.83,.83]){a.box(g,[.14,4.4,.14],[x+dx,2.65,zz],steel);a.cylinder(g,.13,.09,[x+dx,4.91,zz],M.gold);}
  a.box(g,[2.2,.18,4.4],[x,4.82,z],M.brass);
  const screw=new T.Group();g.add(screw);screw.position.set(x,.54,z);a.cylinder(screw,.11,4.25,[0,2.12,0],steel);
  const points=Array.from({length:161},(_,k)=>new T.Vector3(Math.cos(k*Math.PI/8)*.21,k/160*4.15,Math.sin(k*Math.PI/8)*.21));a.mesh(screw,new T.TubeGeometry(new T.CatmullRomCurve3(points),160,.033,5,false),M.gold);jointMotion(a,screw,{mode:'rotate',axis:'y',speed:side*.72});
  const lift=new T.Group();g.add(lift);lift.position.set(x,.55,z);a.box(lift,[1.95,.22,3.5],[0,0,0],M.brass);a.box(lift,[1.35,.9,1.5],[0,.62,0],M.stone);a.box(lift,[1.6,.17,1.78],[0,1.14,0],steel);for(const xx of [-.4,.4])a.box(lift,[.17,.46,.025],[xx,.67,.77],warm);a.clockworkLifts.push(lift);
  const shaft=a.rod(g,[side*4.4,1,-8.7],[x,1,z],.11,steel);shaft.userData.transmission=true;
  a.gear(g,.72,20,[x,.56,3.3],side*.5,M.gold);a.box(g,[1.8,.16,1.8],[x,.22,3.3],steel);
  const beam=new T.Group();g.add(beam);beam.position.set(x,3.3,2.7);a.box(beam,[.18,.18,2.2],[0,0,0],M.brass);a.mesh(beam,new T.SphereGeometry(.15,10,8),M.gold,[0,0,0]);jointMotion(a,beam,{axis:'x',speed:.72,amplitude:.16,phase:side*Math.PI/2});
 }
 for(const side of [-1,1]){a.box(g,[2.1,.15,2.1],[side*8,.25,7.2],steel);a.gear(g,.85,24,[side*8,.5,7.2],side*.28);a.cylinder(g,.11,.9,[side*8,.78,7.2],M.brass);}
 return g;
}
