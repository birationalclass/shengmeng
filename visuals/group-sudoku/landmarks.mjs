import * as T from '../3d/vendor/three.module.js';
import {jointMotion} from './architectural-motion.mjs?v=living1';
import {banner} from './great-wall.mjs?v=living1';
// Architectural vocabulary studied from the Palace Museum, English Heritage,
// UNESCO Chartres, and Kew's iron-and-glass houses (sources in README).
export function landmark(a,parent,type,x,z,scale=1){
 const g=new T.Group();parent.add(g);g.position.set(x,.15,z);g.scale.setScalar(scale);g.userData.landmark=type;const M=a.materials;
 const box=(s,p,m=M.stone)=>a.box(g,s,p,m),cyl=(r,h,p,m=M.stone,r2=r)=>a.cylinder(g,r,h,p,m,r2),rod=(p,q,r=.035,m=M.brass)=>a.rod(g,p,q,r,m);
 const window=(x,y,z,w=.34,h=.63)=>{box([w+.12,h+.12,.08],[x,y,z],M.paper);box([w,h,.03],[x,y,z+.06],M.dark);box([.028,h,.025],[x,y,z+.09],M.brass);box([w,.025,.025],[x,y,z+.09],M.brass);};
 box([2.3,.18,2.2],[0,.1,0]);
 if(type==='well'||type==='fountain'){
  cyl(1.02,.25,[0,.30,0],M.paper);a.torus(g,.93,.12,[0,.48,0],M.stone);cyl(.81,.045,[0,.43,0],new T.MeshStandardMaterial({color:0x537e7a,metalness:.5,roughness:.22}));
  if(type==='fountain'){cyl(.17,1.1,[0,.93,0],M.paper);cyl(.47,.11,[0,1.43,0],M.brass);a.mesh(g,new T.SphereGeometry(.14,12,8),M.gold,[0,1.72,0]);for(let k=0;k<6;k++){const q=k*Math.PI/3;const curve=new T.QuadraticBezierCurve3(new T.Vector3(0,1.62,0),new T.Vector3(Math.sin(q)*.7,1.5,Math.cos(q)*.7),new T.Vector3(Math.sin(q)*.66,.45,Math.cos(q)*.66));a.mesh(g,new T.TubeGeometry(curve,10,.013,4,false),M.paper);const drop=new T.Group();g.add(drop);curve.getPoint(k/6,drop.position);a.mesh(drop,new T.SphereGeometry(.055,7,5),M.paper);jointMotion(a,drop,{mode:'path',curve,speed:.46,phase:k/6});}}
  else{for(const sign of [-1,1])box([.12,1.8,.15],[sign*.77,1.27,0],M.wood);rod([-.91,1.75,0],[.91,1.75,0],.07,M.wood);rod([0,1.75,0],[0,.65,0],.023,M.dark);for(const sign of [-1,1]){const r=box([1.1,.1,1.6],[sign*.44,2.26,0],M.dark);r.rotation.z=-sign*.48;}const bucket=new T.Group();g.add(bucket);bucket.position.y=.57;a.cylinder(bucket,.20,.27,[0,0,0],M.wood);jointMotion(a,bucket,{mode:'lift',property:'position',axis:'y',speed:.7,amplitude:.55});const crank=new T.Group();crank.position.set(.94,1.75,0);g.add(crank);a.torus(crank,.25,.035,[0,0,0],M.brass,[0,Math.PI/2,0]);a.rod(crank,[0,-.25,0],[0,.25,0],.025,M.wood);a.rod(crank,[0,0,-.25],[0,0,.25],.025,M.wood);jointMotion(a,crank,{mode:'rotate',axis:'x',speed:.7});}
 }
 if(type==='pavilion'){
  cyl(1.28,.18,[0,.28,0],M.paper);for(let k=0;k<6;k++){const q=k*Math.PI/3,px=Math.sin(q)*.92,pz=Math.cos(q)*.92;cyl(.085,1.7,[px,1.15,pz],M.wood);for(let j=0;j<3;j++)box([.21+j*.12,.065,.21+j*.12],[px,1.84+j*.09,pz],M.brass);const q2=q+Math.PI/3;rod([px,.7,pz],[Math.sin(q2)*.92,.7,Math.cos(q2)*.92],.035,M.wood);}
  for(let tier=0;tier<2;tier++){const r=tier?1.00:1.48,y=tier?2.9:2.17;a.mesh(g,new T.ConeGeometry(r,.52,6),M.jade,[0,y,0]);for(let k=0;k<6;k++){const q=k*Math.PI/3;rod([0,y+.28,0],[Math.sin(q)*r,y-.17,Math.cos(q)*r],.035,M.brass);}}cyl(.04,.48,[0,3.38,0],M.gold);
 }
 if(type==='market'){
  for(const px of [-.9,.9])for(const pz of [-.7,.7])box([.1,1.7,.1],[px,1.1,pz],M.wood);
  box([1.9,.15,1.25],[0,.85,0],M.wood);for(let k=0;k<8;k++){const m=k%2?M.paper:M.red;const r=box([.26,.08,1.85],[-.91+k*.26,1.97,0],m);r.rotation.x=.12;box([.26,.22,.035],[-.91+k*.26,1.72,.9],m);}
  for(let k=0;k<3;k++){box([.43,.35,.48],[-.6+k*.6,1.13,0],M.wood);for(let j=0;j<4;j++)a.mesh(g,new T.SphereGeometry(.085,7,5),j%2?M.gold:M.red,[-.7+k*.6+(j%2)*.18,1.36,(j<2?-.12:.10)]);}
 }
 if(type==='windmill'){
  cyl(.70,2.3,[0,1.4,0],M.paper,.94);a.mesh(g,new T.ConeGeometry(.92,.95,8),M.dark,[0,3.02,0]);window(0,1.2,.82,.30,.63);for(let y=.55;y<2.6;y+=.4)a.torus(g,.86-(y-.55)*.1,.026,[0,y,0],M.wood);
  const sails=new T.Group();g.add(sails);sails.position.set(0,2.18,.85);for(let k=0;k<4;k++){const arm=new T.Group();sails.add(arm);arm.rotation.z=k*Math.PI/2;a.box(arm,[.10,1.85,.07],[0,.85,0],M.wood);for(const px of [0,.4])a.box(arm,[.04,1.1,.035],[px,1.2,0],M.wood);for(let j=0;j<7;j++)a.box(arm,[.46,.025,.04],[.2,.69+j*.16,0],M.paper);}a.mesh(sails,new T.SphereGeometry(.14,10,8),M.brass);a.detailMotion??=[];a.detailMotion.push({object:sails,axis:'z',speed:.22});
 }
 if(type==='clocktower'){
  box([1.5,3.5,1.35],[0,1.97,0]);for(const y of [.43,1.5,2.6,3.65])box([1.72,.11,1.57],[0,y,0],M.paper);for(const px of [-.62,.62])box([.11,3.5,.09],[px,2,.72],M.paper);window(0,1.12,.72,.32,.70);
  const face=new T.Group();g.add(face);face.position.set(0,2.95,.77);const plate=a.cylinder(face,.50,.05,[0,0,0],M.dark);plate.rotation.x=Math.PI/2;a.torus(face,.50,.035,[0,0,.04],M.gold,[0,0,0]);for(let k=0;k<12;k++){const q=k*Math.PI/6;const tick=a.box(face,[.022,.085,.025],[Math.sin(q)*.40,Math.cos(q)*.40,.06],M.gold);tick.rotation.z=-q;}for(const [length,speed]of [[.29,-.035],[.39,-.16]]){const hand=new T.Group();hand.position.z=.08;face.add(hand);a.rod(hand,[0,0,0],[0,length,0],.018,M.paper);jointMotion(a,hand,{mode:'rotate',axis:'z',speed});}
  a.mesh(g,new T.ConeGeometry(1.11,1.20,4),M.jade,[0,4.35,0]).rotation.y=Math.PI/4;cyl(.04,.40,[0,5.1,0],M.gold);
 }
 if(type==='greenhouse'){
  box([2.2,.55,2.3],[0,.49,0],M.paper);const glass=new T.MeshPhysicalMaterial({color:0x93b3a2,transparent:true,opacity:.32,metalness:.18,roughness:.18,side:T.DoubleSide,depthWrite:false});
  const skin=a.mesh(g,new T.CylinderGeometry(1.05,1.05,2.12,24,1,true,Math.PI/2,Math.PI),glass,[0,1.15,0]);skin.rotation.x=Math.PI/2;
  for(let j=0;j<8;j++){const zz=-1.06+j*.303;const pts=Array.from({length:17},(_,k)=>new T.Vector3(Math.cos(k*Math.PI/16)*1.05,1.15+Math.sin(k*Math.PI/16)*1.05,zz));a.mesh(g,new T.TubeGeometry(new T.CatmullRomCurve3(pts),16,.027,5,false),M.brass);}
  for(let k=0;k<7;k++){const q=k*Math.PI/6;rod([Math.cos(q)*1.05,1.15+Math.sin(q)*1.05,-1.08],[Math.cos(q)*1.05,1.15+Math.sin(q)*1.05,1.08],.019);}
  for(const px of [-.6,.6])for(const zz of [-.7,0,.7]){cyl(.17,.28,[px,.80,zz],M.red);a.mesh(g,new T.IcosahedronGeometry(.26,0),M.jade,[px,1.13,zz]);}
 }
 if(type==='observatory'){
  cyl(1.02,1.5,[0,1,0],M.stone);for(let k=0;k<10;k++){const q=k*Math.PI/5;const pp=[Math.sin(q)*1.01,1,Math.cos(q)*1.01];box([.14,.8,.08],pp,M.paper).rotation.y=q;}
  const domeStart=g.children.length;cyl(1.17,.13,[0,1.82,0],M.brass);a.mesh(g,new T.SphereGeometry(1.08,24,12,0,Math.PI*2,0,Math.PI/2),M.jade,[0,1.88,0]);for(const sign of [-1,1]){const pts=Array.from({length:17},(_,k)=>new T.Vector3(sign*.17,1.88+Math.sin(k*Math.PI/16)*1.08,Math.cos(k*Math.PI/16)*1.06));a.mesh(g,new T.TubeGeometry(new T.CatmullRomCurve3(pts),16,.035,5,false),M.brass);}rod([0,2.03,0],[0,2.76,1.20],.10,M.dark);rod([0,2.74,1.16],[0,2.88,1.4],.14,M.brass);const dome=new T.Group();for(const part of g.children.slice(domeStart))dome.add(part);g.add(dome);jointMotion(a,dome,{mode:'rotate',axis:'y',speed:.12});
 }
 if(type==='obelisk'){
  box([1.35,.23,1.25],[0,.31,0],M.paper);const mast=a.mesh(g,new T.CylinderGeometry(.25,.42,2.1,4),M.stone,[0,1.47,0]);mast.rotation.y=Math.PI/4;a.mesh(g,new T.ConeGeometry(.35,.45,4),M.gold,[0,2.75,0]).rotation.y=Math.PI/4;for(let y=.9;y<2.3;y+=.26)box([.19,.025,.03],[0,y,.29],M.brass);
 }
 if(type==='gatehouse'){
  for(const px of [-.83,.83]){cyl(.47,2,[px,1.3,0]);cyl(.57,.14,[px,2.38,0],M.paper);for(let k=0;k<6;k++){const q=k*Math.PI/3;box([.17,.28,.17],[px+Math.sin(q)*.43,2.61,Math.cos(q)*.43],M.stone);}window(px,1.55,.46,.18,.46);}box([1.2,.5,.64],[0,1.85,0]);for(let k=-3;k<=3;k++)rod([k*.11,.3,.35],[k*.11,1.65,.35],.021,M.wood);for(const y of [.55,.95,1.35])rod([-.40,y,.35],[.40,y,.35],.024,M.wood);
 }
 if(type==='pavilion'){
  for(const px of [-.72,.72]){const lamp=new T.Group();lamp.position.set(px,1.88,.57);g.add(lamp);a.rod(lamp,[0,0,0],[0,-.31,0],.02,M.brass);a.mesh(lamp,new T.SphereGeometry(.14,8,6),M.red,[0,-.40,0]);a.rod(lamp,[0,-.52,0],[0,-.66,0],.014,M.gold);jointMotion(a,lamp,{axis:'z',speed:1.35,amplitude:.17,phase:px});}
  const vane=new T.Group();vane.position.y=3.55;g.add(vane);a.rod(vane,[-.43,0,0],[.43,0,0],.03,M.brass);const arrow=a.mesh(vane,new T.ConeGeometry(.13,.26,3),M.gold,[.43,0,0]);arrow.rotation.z=-Math.PI/2;jointMotion(a,vane,{mode:'rotate',axis:'y',speed:.23});
 }
 if(type==='market')banner(a,g,.83,1.92,-.5,x*.1);
 if(type==='clocktower'){
  const pendulum=new T.Group();pendulum.position.set(0,1.46,.87);g.add(pendulum);a.rod(pendulum,[0,0,0],[0,-.63,0],.022,M.brass);const bob=a.cylinder(pendulum,.14,.045,[0,-.63,0],M.gold);bob.rotation.x=Math.PI/2;jointMotion(a,pendulum,{axis:'z',speed:1.8,amplitude:.20});
 }
 if(type==='greenhouse'){
  for(const side of [-1,1]){const vent=new T.Group();vent.position.set(side*.3,2.13,0);vent.rotation.z=-side*.4;g.add(vent);a.box(vent,[.55,.045,1.22],[side*.26,0,0],M.brass);a.box(vent,[.47,.05,1.10],[side*.26,.027,0],new T.MeshStandardMaterial({color:0x87a699,transparent:true,opacity:.5,roughness:.2}));jointMotion(a,vent,{axis:'z',speed:.48,amplitude:.14,phase:side});}
 }
 if(type==='gatehouse')banner(a,g,-.83,2.58,0,z*.1);
 return g;
}
