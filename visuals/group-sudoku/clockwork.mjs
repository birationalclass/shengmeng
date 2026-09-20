import {installWorkshopClock} from './workshop-clock.mjs?v=clock1';
import * as T from '../3d/vendor/three.module.js';
export const GEAR_TEETH=[28,20,28,32,24];
export function gearTrain(){let x=0;const gears=GEAR_TEETH.map((teeth,i)=>{const radius=teeth*.035;if(i)x+=(GEAR_TEETH[i-1]+teeth)*.035;return {teeth,radius,x,speed:.36*28/teeth*(i%2?-1:1)};});const center=(gears[0].x+gears.at(-1).x)/2;return gears.map(g=>({...g,x:g.x-center}));}
export function compoundGearTrain(){const list=gearTrain().map(g=>({...g,z:0,parent:null}));for(let i=0;i<5;i++){const base=list[i];for(const sign of [-1,1]){const index=list.length,r=.28,z=sign*(base.radius+r),speed=-base.speed*base.radius/r;list.push({x:base.x,z,radius:r,teeth:8,speed,parent:i});if(sign<0)for(const direction of [-1,1])list.push({x:base.x+direction*(r+.21),z,radius:.21,teeth:6,speed:-speed*r/.21,parent:index});}}return list;}
export function crankSlider(theta,r=.42,length=1.8){const x=r*Math.sin(theta),y=r*Math.cos(theta);return {x,y,slider:y+Math.sqrt(length*length-x*x)};}
export function clockworkCity(a,p){
 p.userData.domain='precision-clockwork-workshop';const g=new T.Group();p.add(g);const M=a.materials;
 const steel=new T.MeshStandardMaterial({color:0x34454b,metalness:.8,roughness:.35}),copper=new T.MeshStandardMaterial({color:0x955c3e,metalness:.6,roughness:.4}),warm=new T.MeshStandardMaterial({color:0xffd59a,emissive:0xff8b37,emissiveIntensity:1.2}),silver=new T.MeshStandardMaterial({color:0xb8c6c3,metalness:.8,roughness:.3});
 const group=(x,y,z,name)=>{const q=new T.Group();q.position.set(x,y,z);q.userData.landmark=name;g.add(q);return q;};
 a.machineMotion=[];
 function wheel(parent,spec,phase=0){const w=a.gear(parent,spec.radius*1.055,spec.teeth,[spec.x,0,spec.z||0],spec.speed,phase%3===0?copper:phase%3===1?M.brass:silver);w.userData.phase=phase%2?Math.PI/spec.teeth:0;w.userData.gearTrain=spec;a.cylinder(parent,.065,.58,[spec.x,.14,spec.z||0],steel);a.cylinder(parent,.10,.04,[spec.x,.47,spec.z||0],M.gold);return w;}
 // 25 exposed meshing wheels in a main row and branching upper/lower reducers.
 a.box(g,[11.4,.30,3],[0,.25,-8.6],steel);
 for(const x of [-5.35,0,5.35]){a.box(g,[.18,5.3,.24],[x,2.85,-8.9],steel);for(const y of [.8,2.4,4.8])a.box(g,[.40,.11,.45],[x,y,-8.9],M.brass);}
 for(const y of [.7,4.9])a.box(g,[11.2,.17,.3],[0,y,-8.9],steel);
 for(const side of [-1,1])a.rod(g,[side*5.3,.6,-8.9],[0,4.9,-8.9],.045,copper);
 const face=group(0,2.65,-8.20,'compound-transmission-wall');face.rotation.x=Math.PI/2;
 compoundGearTrain().forEach((spec,i)=>wheel(face,spec,i));
 // Parallel rear shaft: a readable depth layer behind the small front wheels.
 for(const side of [-1,1]){const rear=group(side*3.25,4.20,-8.78,'secondary-flywheel');rear.rotation.x=Math.PI/2;wheel(rear,{x:0,radius:.76,teeth:22,speed:side*.30},1);}
 // Left: riveted boiler, firebox, pipes, flywheel and working piston.
 const engine=group(-9.15,.18,-.4,'steam-power-unit');a.box(engine,[2.65,.28,5.6],[0,.18,0],steel);
 a.cylinder(engine,.87,2.90,[0,1.88,-.4],copper);for(const y of [.52,1.10,2.15,3.30])a.torus(engine,.89,.055,[0,y,-.4],M.brass);
 a.mesh(engine,new T.SphereGeometry(.88,20,10,0,Math.PI*2,0,Math.PI/2),copper,[0,3.30,-.4]);
 for(let j=0;j<16;j++){const q=j*Math.PI/8;for(const y of [1.08,2.12,3.27])a.mesh(engine,new T.SphereGeometry(.038,5,4),silver,[Math.sin(q)*.90,y,-.4+Math.cos(q)*.90]);}
 a.box(engine,[1.1,.9,.4],[0,.79,.56],steel);a.box(engine,[.72,.48,.045],[0,.75,.79],warm);for(let j=-2;j<=2;j++)a.box(engine,[.045,.55,.06],[j*.14,.75,.83],steel);
 a.cylinder(engine,.20,1.4,[0,4.05,-.4],steel);a.torus(engine,.24,.05,[0,4.7,-.4],M.brass);
 for(const x of [-.66,.66]){a.rod(engine,[x,2.70,-.3],[x,2.70,1.6],.085,copper);a.rod(engine,[x,2.70,1.6],[x,1.25,1.6],.085,copper);for(const z of [.4,1.2])a.torus(engine,.12,.035,[x,2.7,z],M.brass,[Math.PI/2,0,0]);}
 const gauge=a.cylinder(engine,.23,.07,[0,2.52,.51],M.paper);gauge.rotation.x=Math.PI/2;const needle=new T.Group();needle.position.set(0,2.52,.57);engine.add(needle);a.rod(needle,[0,0,0],[.10,.12,0],.018,steel);
 // Crank pin and connecting rod obey a slider-crank linkage, rather than independent sways.
 const crank=group(-9.15,1.18,3.00,'steam-crankshaft');const wheelFace=new T.Group();crank.add(wheelFace);wheelFace.rotation.x=Math.PI/2;wheel(wheelFace,{x:0,radius:1.03,teeth:30,speed:.72});
 const dynamic=new T.Group();crank.add(dynamic);const pin=a.mesh(dynamic,new T.SphereGeometry(.12,8,6),M.gold),rod=a.cylinder(dynamic,.06,1,[0,0,0],silver),piston=new T.Group();dynamic.add(piston);a.box(piston,[.46,.33,.38],[0,0,0],silver);a.box(piston,[.10,.87,.10],[0,.56,0],M.brass);
 a.box(crank,[.7,.70,.7],[0,2.95,-.09],steel);a.box(crank,[.50,.50,.15],[0,2.95,.34],copper);a.machineMotion.push({kind:'piston',root:dynamic,pin,rod,piston});
 // Right: open gantry, toothed rack and a visibly useful cargo hoist.
 const hoist=group(9.10,.18,.3,'rack-and-pinion-cargo-hoist');a.box(hoist,[2.70,.26,6],[0,.18,0],steel);
 for(const x of [-1.03,1.03])for(const z of [-1.8,1.8]){a.box(hoist,[.16,4.8,.16],[x,2.65,z],steel);a.box(hoist,[.4,.10,.40],[x,.44,z],M.brass);}
 for(const z of [-1.8,1.8])a.box(hoist,[2.5,.18,.18],[0,4.97,z],M.brass);for(const x of [-1.1,1.1])a.box(hoist,[.18,.18,4.3],[x,4.97,0],M.brass);for(const x of [-1.03,1.03]){a.rod(hoist,[x,.6,-1.8],[x,4.8,1.8],.045,copper);a.rod(hoist,[x,.6,1.8],[x,4.8,-1.8],.045,copper);}
 const lift=new T.Group();hoist.add(lift);a.box(lift,[1.8,.19,3.1],[0,0,0],M.brass);a.box(lift,[1.0,.85,1.25],[0,.53,0],steel);for(const z of [-.45,.45])a.box(lift,[1.07,.07,.10],[0,.5,z],copper);const rack=a.box(lift,[.14,3.25,.14],[.8,1.22,-1.45],silver);for(let j=0;j<27;j++)a.box(lift,[.11,.065,.15],[.91,-.34+j*.12,-1.45],M.gold);
 for(const x of [-.75,.75])a.rod(lift,[x,.15,1.25],[x,.61,1.25],.035,steel);a.rod(lift,[-.75,.61,1.25],[.75,.61,1.25],.035,steel);
 a.machineMotion.push({kind:'hoist',root:lift});for(const side of [-1,1]){const cable=a.cylinder(hoist,.026,1,[side*.72,3,0],copper);a.machineMotion.push({kind:'cable',root:cable});const pulley=a.cylinder(hoist,.25,.15,[side*.72,4.85,0],M.gold);pulley.rotation.z=Math.PI/2;}const hoistFace=new T.Group();hoist.add(hoistFace);hoistFace.position.set(.55,2.0,-1.17);hoistFace.rotation.x=Math.PI/2;const pinion=wheel(hoistFace,{x:0,radius:.39,teeth:12,speed:0},1);a.machineMotion.push({kind:'pinion',root:pinion});
 // Five-geared side reducers route power around the board, with exposed shafting.
 for(const side of [-1,1]){const bank=group(side*8.10,1.90,-5.90,side<0?'input-reduction-gears':'output-reduction-gears');bank.rotation.x=Math.PI/2;for(let j=0;j<5;j++)wheel(bank,{x:(j-2)*.63,radius:.315,teeth:9,speed:.8*(j%2?-1:1)},j);a.rod(g,[side*4.65,2.45,-8.4],[side*8.10,1.90,-5.90],.105,copper);a.rod(g,[side*9.1,1.9,-5.9],[side*9.1,1.9,-2.6],.10,steel);for(const z of [-4.4,-3.0]){a.box(g,[.5,1.4,.32],[side*9.1,1.0,z],steel);a.torus(g,.19,.06,[side*9.1,1.9,z],M.brass,[Math.PI/2,0,0]);}}
 // Eight visible spur gears form a low foreground service train.
 const foreground=group(0,.42,9.5,'foreground-service-transmission');a.box(foreground,[9,.15,1.4],[0,-.20,0],steel);for(let j=0;j<8;j++)wheel(foreground,{x:(j-3.5)*1.05,radius:.525,teeth:15,speed:.40*(j%2?-1:1)},j);
 // Ground-level direction marks show the energy route without walls masking it.
 for(const side of [-1,1])for(let j=0;j<3;j++){const arrow=a.mesh(g,new T.ConeGeometry(.13,.38,3),M.gold,[side*7.8,.30,4.4+j*.7]);arrow.rotation.x=side*Math.PI/2;}
 if(typeof document!=='undefined'){a.plate(g,'STEAM / 动力',[-9.15,.39,5.75],2.55,.7);a.plate(g,'HOIST / 升降',[9.10,.39,5.75],2.55,.7);}
 installWorkshopClock(a,g);updateClockwork(a.machineMotion,0,true);return g;
}
export function updateClockwork(tracks,time,reduced){const theta=reduced?0:time*.72;for(const m of tracks||[]){if(m.kind==='piston'){const q=crankSlider(-theta);m.pin.position.set(q.x,q.y,.32);m.piston.position.set(0,q.slider,.32);const start=new T.Vector3(q.x,q.y,.32),end=new T.Vector3(0,q.slider,.32),delta=end.clone().sub(start);m.rod.position.copy(start.add(end).multiplyScalar(.5));m.rod.scale.y=delta.length();m.rod.quaternion.setFromUnitVectors(new T.Vector3(0,1,0),delta.normalize());}else if(m.kind==='hoist'){m.root.position.y=.65+(reduced?0:(1-Math.cos(theta))*.72);}else if(m.kind==='cable'){const floor=.78+(reduced?0:(1-Math.cos(theta))*.72);m.root.position.y=(4.85+floor)/2;m.root.scale.y=4.85-floor;}else if(m.kind==='pinion'){m.root.rotation.y=-(reduced?0:(1-Math.cos(theta))*.72)/.39;}}}
