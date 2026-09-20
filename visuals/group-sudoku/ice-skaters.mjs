import * as T from '../3d/vendor/three.module.js';
const TAU=Math.PI*2;
export function skatingPose(time,index){
 const angle=time*.17+index*Math.PI+.10*Math.sin(time*.23+index),radius=9.12+.12*Math.sin(angle*3+index),x=Math.sin(angle)*radius,z=Math.cos(angle)*radius;
 const cycle=((time+index*8)%22+22)%22,spin=Math.max(0,Math.min(1,(cycle-15)/2.6));
 // One complete turn returns to the tangent without an orientation discontinuity.
 return {x,z,heading:angle+Math.PI/2-TAU*(spin*spin*(3-2*spin)),spin:cycle>=15&&cycle<=17.6,stride:Math.sin(time*2.1+index*Math.PI),lean:.13*Math.sin(time*.9+index)};
}
export function installIceSkaters(a,parent){
 const iceY=.315,metal=new T.MeshStandardMaterial({color:0xdbe9ee,metalness:.86,roughness:.22}),boot=new T.MeshStandardMaterial({color:0x162d3c,roughness:.65}),skin=new T.MeshStandardMaterial({color:0xe4c0a1,roughness:.85}),wool=new T.MeshStandardMaterial({color:0xe0e5d7,roughness:.9});
 a.iceSkaters=[];
 for(let i=0;i<2;i++){
  const coat=new T.MeshStandardMaterial({color:i?0x26546a:0x863d4d,roughness:.76}),root=new T.Group(),body=new T.Group();parent.add(root);root.position.y=iceY;root.scale.setScalar(1.12);root.add(body);root.userData.skater=i;
  a.mesh(body,new T.ConeGeometry(.23,.5,10),coat,[0,.80,0]);a.mesh(body,new T.SphereGeometry(.13,12,10),skin,[0,1.17,.025]);
  const cap=a.mesh(body,new T.SphereGeometry(.14,12,8),coat,[0,1.27,.015]);cap.scale.y=.62;a.mesh(body,new T.SphereGeometry(.05,8,6),wool,[0,1.37,.01]);a.torus(body,.092,.025,[0,1.035,0],wool);
  const scarf=a.box(body,[.08,.035,.35],[.09,1.01,-.15],wool);scarf.rotation.x=.19;
  const arms=[],legs=[];
  for(const side of [-1,1]){
   const arm=new T.Group();arm.position.set(side*.16,.96,0);body.add(arm);a.rod(arm,[0,0,0],[side*.24,-.10,.03],.048,coat);a.rod(arm,[side*.24,-.10,.03],[side*.40,-.07,.16],.038,coat);a.mesh(arm,new T.SphereGeometry(.05,8,6),wool,[side*.41,-.07,.16]);arms.push(arm);
   const leg=new T.Group();leg.position.set(side*.095,.59,0);root.add(leg);a.rod(leg,[0,0,0],[side*.025,-.25,.035],.054,boot);a.rod(leg,[side*.025,-.25,.035],[side*.04,-.50,0],.044,boot);a.box(leg,[.105,.095,.24],[side*.04,-.515,.075],boot);a.rod(leg,[side*.04,-.575,-.04],[side*.04,-.575,.22],.013,metal);legs.push(leg);
  }
  const geometry=new T.BufferGeometry();geometry.setAttribute('position',new T.Float32BufferAttribute(new Float32Array(70*3),3));const trail=new T.Line(geometry,new T.LineBasicMaterial({color:0xf3fdff,transparent:true,opacity:.27,depthWrite:false}));trail.frustumCulled=false;parent.add(trail);
  a.iceSkaters.push({root,body,arms,legs,trail,index:i,iceY});
 }
 updateIceSkaters(a.iceSkaters,0,true);
}
export function updateIceSkaters(skaters,time,reduced=false){
 for(const skater of skaters||[]){const {root,body,arms,legs,trail,index,iceY}=skater,t=reduced?0:time,p=skatingPose(t,index);root.position.set(p.x,iceY,p.z);root.rotation.y=p.heading;body.rotation.z=reduced?0:p.lean;body.rotation.x=reduced?0:.10;arms.forEach((arm,j)=>{arm.rotation.x=reduced?0:.25*Math.sin(t*.8+j);arm.rotation.y=p.spin?(j?-.9:.9):.1*Math.sin(t*.7+j);});legs.forEach((leg,j)=>{leg.rotation.x=reduced?0:(j?-.20:.20)*p.stride;leg.rotation.z=reduced?0:(j?-.1:.1)*(1+p.stride)*.35;});
  trail.visible=!reduced;const positions=trail.geometry.attributes.position;for(let k=0;k<positions.count;k++){const old=skatingPose(t-(positions.count-1-k)*.025,index);positions.setXYZ(k,old.x,iceY+.007,old.z);}positions.needsUpdate=true;
 }
}
