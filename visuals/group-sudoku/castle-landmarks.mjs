import * as T from '../3d/vendor/three.module.js';
import {jointMotion} from './architectural-motion.mjs?v=living1';
import {installOwls} from './owls.mjs?v=owl-clearance1';
// Reference silhouettes from BV1Dw411E7dY, adapted around an unobstructed board.
function rock(a,p,x,z,h,rx,rz,M){
 a.cliffMaterial??=new T.MeshStandardMaterial({color:0x626861,roughness:.97,flatShading:true});
 const geo=new T.CylinderGeometry(.60,1,h,9,5),v=geo.attributes.position;
 for(let i=0;i<v.count;i++){const y=v.getY(i),q=Math.atan2(v.getZ(i),v.getX(i)),n=1+.12*Math.sin(q*7+y*6+x);v.setXYZ(i,v.getX(i)*n,y,v.getZ(i)*n);}
 geo.computeVertexNormals();const o=a.mesh(p,geo,a.cliffMaterial,[x,h/2,z]);o.scale.set(rx,1,rz);o.rotation.y=x*.43;return o;
}
function crenels(a,p,x,z,r,y,M,n=12){for(let k=0;k<n;k++){const q=k*Math.PI*2/n;const b=a.box(p,[.20,.30,.22],[x+Math.sin(q)*r,y,z+Math.cos(q)*r],M);b.rotation.y=q;}}
function coveredBridge(a,p,x,z,length,K){const {M,group}=K,g=group(p,x,z);g.userData.landmark='covered-gothic-bridge';
 a.box(g,[length,.18,.92],[0,1.75,0],M.limestone);
 for(let j=0;j<=10;j++){const xx=-length/2+j*length/10;for(const s of [-1,1]){a.box(g,[.085,1.75,.085],[xx,2.67,s*.41],a.materials.wood);if(j<10){a.rod(g,[xx,2.25,s*.41],[xx+length/20,3.45,s*.41],.045,a.materials.wood);a.rod(g,[xx+length/20,3.45,s*.41],[xx+length/10,2.25,s*.41],.045,a.materials.wood);}}}
 for(const s of [-1,1]){const roof=a.box(g,[length+.35,.1,.74],[0,3.73,s*.25],M.slate);roof.rotation.x=s*.65;}
 for(const xx of [-length*.4,0,length*.4])a.box(g,[.45,1.65,.7],[xx,.82,0],M.limestone);return g;
}
// Sloped stone walks join actual landing points, with piers down to the platform.
function stoneWalk(a,p,from,to,K,width=.9){
 const M=K.M,dx=to[0]-from[0],dz=to[2]-from[2],dy=to[1]-from[1],run=Math.hypot(dx,dz),length=Math.hypot(run,dy);
 const g=new T.Group();g.userData.landmark='connected-stone-walk';g.position.set((from[0]+to[0])/2,(from[1]+to[1])/2,(from[2]+to[2])/2);g.rotation.y=Math.atan2(dx,dz);p.add(g);
 const deck=new T.Group();deck.rotation.x=-Math.atan2(dy,run);g.add(deck);
 a.box(deck,[width,.18,length+.12],[0,-.09,0],M.limestone);
 for(const side of [-1,1]){a.box(deck,[.11,.13,length],[side*(width-.1)/2,.49,0],M.limestone);for(let j=0;j<=Math.ceil(length/.6);j++)a.box(deck,[.09,.48,.09],[side*(width-.1)/2,.24,-length/2+j*length/Math.ceil(length/.6)],M.limestone);}
 for(let j=0;j<=Math.ceil(run/1.6);j++){const t=j/Math.ceil(run/1.6),h=from[1]+dy*t-.18;a.box(p,[.38,h,.42],[from[0]+dx*t,h/2,from[2]+dz*t],M.limestone);}
 return g;
}
export function hogwarts(a,p,K){const {M,group,spire,hall,arch}=K;p.userData.domain='enchanted-academy';
 // Uneven rocky foundations, dominant round tower and a low, long Great Hall.
 for(const [x,z,h,rx,rz]of [[-6.7,-8.1,1.6,1.9,1.6],[.3,-9.0,1.3,3.2,1.7],[7.8,-5.4,2.2,1.55,2.0],[-8.1,.2,1.4,1.8,2.9]])rock(a,p,x,z,h,rx,rz,M.dark);
 const keep=spire(a,p,-6.5,-7.5,6.3,1.18);keep.position.y=1.05;keep.userData.landmark='dominant-round-tower';
 for(let j=0;j<4;j++){const q=j*Math.PI/2;const turret=spire(a,keep,Math.sin(q)*1.03,Math.cos(q)*1.03,1.25,.26);turret.position.y=5.3;}
 const great=hall(a,p,.25,-8.5,7.1,3.3);great.position.y=1.0;
 const tall=spire(a,p,5.5,-8.6,5.7,.61);tall.position.y=.9;spire(a,p,7.6,-5.8,4.2,.86).position.y=1.8;
 const annex=hall(a,p,-8.3,-1.8,4.9,2.6);annex.rotation.y=Math.PI/2;annex.position.y=.9;
 spire(a,p,-8.1,2.0,3.6,.7).position.y=.6;spire(a,p,8.3,.4,3.4,.53);
 // Run the covered gallery from the east tower to a supported gate pavilion.
 const bridge=coveredBridge(a,p,8.3,3.5,5.1,K);bridge.rotation.y=Math.PI/2;
 const gate=hall(a,p,8.3,6.65,1.8,1.8);gate.position.y=.15;gate.userData.landmark='gallery-gatehouse';
 stoneWalk(a,p,[7.6,1.95,-5.1],[8.3,1.99,-.05],K);
 stoneWalk(a,p,[5.5,1.15,-8.6],[7.6,1.95,-6.35],K);
 stoneWalk(a,p,[3.6,1.25,-8.5],[5.5,1.15,-8.6],K);
 stoneWalk(a,p,[-5.55,1.3,-7.5],[-3.2,1.25,-8.5],K);
 stoneWalk(a,p,[-7.35,1.3,-7.1],[-8.3,1.15,-4.1],K);
 stoneWalk(a,p,[-8.3,1.15,.35],[-8.1,.85,1.5],K);
 const court=group(p,-.3,-11.05);for(let j=0;j<8;j++){const x=-3.1+j*.88;a.box(court,[.16,1.25,.35],[x,.76,0],M.limestone);if(j<7)arch(a,court,x+.44,.35,.12,.70,.96,M.limestone,M.dark);}a.box(court,[6.6,.17,.68],[0,1.42,0],M.slate);
 // Steep pitched roofs get small dormers, stone buttresses, and warm tracery.
 for(let j=0;j<5;j++){const x=-2.35+j*1.3;arch(a,great,x,3.5,.84,.35,.64,M.limestone,M.window);a.mesh(great,new T.ConeGeometry(.32,.43,4),M.slate,[x,4.23,.82]).rotation.y=Math.PI/4;}
 installOwls(a,p);
}
export function whiteCity(a,p,K){const {M,spire,hall}=K;p.userData.domain='seven-tier-white-city';
 // Seven ascending semicircular bastions, with the citadel at the summit.
 for(let level=0;level<7;level++){
  const r=5.75-level*.54,y=.2+level*.48,shape=new T.Shape();shape.moveTo(-r,0);shape.absarc(0,0,r,Math.PI,0,true);shape.lineTo(-r,0);
  const terrace=a.mesh(p,new T.ExtrudeGeometry(shape,{depth:.42,bevelEnabled:false,curveSegments:28}),M.limestone,[0,y,-6.22]);terrace.rotation.x=-Math.PI/2;terrace.userData.landmark='white-city-terrace';
  for(let j=0;j<=22;j++){const q=-Math.PI/2+j*Math.PI/22,x=Math.sin(q)*r,z=-6.22-Math.cos(q)*r;const wall=a.box(p,[Math.PI*r/22+.04,.54,.16],[x,y+.35,z],M.limestone);wall.rotation.y=-q;
   if(j%2===0)a.box(p,[.20,.19,.23],[x,y+.71,z],a.materials.paper);
   if(level%2===0&&j%4===0)a.box(p,[.07,.25,.035],[x,y+.30,z+.10],M.dark);
   if(j>1&&j<21&&j%2===0){const r2=r-.30,xx=Math.sin(q)*r2,zz=-6.22-Math.cos(q)*r2,hh=.32+(j%3)*.12;const home=a.box(p,[.28,hh,.29],[xx,y+.42+hh/2,zz],M.limestone);home.rotation.y=-q;const roof=a.mesh(p,new T.ConeGeometry(.24,.18,4),M.slate,[xx,y+.45+hh+.08,zz]);roof.rotation.y=Math.PI/4-q;a.box(p,[.055,.12,.035],[xx,y+.48+hh/2,zz+.16],M.dark);}
  }
 }
 a.box(p,[.73,3.7,.8],[.2,5.22,-8.4],M.limestone);for(const dx of [-.39,.39])for(const dz of [-.42,.42])a.box(p,[.12,4.1,.12],[.2+dx,5.27,-8.4+dz],M.limestone);for(let j=0;j<4;j++)a.box(p,[.12,.35,.04],[.2,4.1+j*.68,-7.98],M.dark);a.box(p,[.92,.18,.98],[.2,7.1,-8.4],M.limestone);const palace=hall(a,p,-1.2,-8.4,2.0,1.15);palace.position.y=3.5;
 // The stone prow cuts through the ascending city terraces.
 const blade=new T.Shape();blade.moveTo(-.2,0);blade.lineTo(.2,0);blade.lineTo(.06,5.3);blade.lineTo(-.06,5.3);blade.closePath();const prow=a.mesh(p,new T.ExtrudeGeometry(blade,{depth:3.2,bevelEnabled:false}),M.limestone,[0,.2,-10.2]);prow.userData.landmark='stone-prow';
 for(const s of [-1,1]){const wing=hall(a,p,s*8.3,-2.4,5.2,1.65);wing.rotation.y=s*Math.PI/2;for(const z of [1.5,5.2]){a.cylinder(p,.65,2.7,[s*8.3,1.5,z],M.limestone);crenels(a,p,s*8.3,z,.61,3.0,M.limestone);}}
}
export function icePalace(a,p,K){const {M,group}=K,root=group(p,0,-10.95);root.userData.landmark='white-witch-ice-palace';
 // A forest of narrow, irregular frozen ribs. The skating lane stays in front.
 for(let j=-5;j<=5;j++){const x=j*.65,h=4.0+2.6*Math.exp(-x*x/3)+.45*Math.sin(j*7);a.mesh(root,new T.CylinderGeometry(.14,.32,h,6),M.ice,[x,h/2,0]);a.mesh(root,new T.ConeGeometry(.29,1.6,6),M.ice,[x,h+.6,0]);
  if(j>-5){const xx=x-.325;a.rod(root,[x,h*.65,0],[xx,h*.83,.2],.10,M.ice);a.rod(root,[xx,h*.83,.2],[x-.65,h*.65,0],.10,M.ice);}}
 for(const s of [-1,1]){for(let j=0;j<4;j++){const x=s*(3.1+j*.6),z=.2+j*.33,h=4.6-j*.6;const shard=a.mesh(root,new T.ConeGeometry(.36,h,5),M.ice,[x,h/2,z]);shard.rotation.z=-s*.09;}
  const points=[[s*2.05,0,.82],[s*2.05,2.7,.82],[s*1.2,4.2,.82],[0,5.2,.82]].map(v=>new T.Vector3(...v));a.mesh(root,new T.TubeGeometry(new T.CatmullRomCurve3(points),18,.18,5,false),M.blue);
 }
 for(let j=-3;j<=3;j++){const h=.65+(.5+.5*Math.sin(j*9))*.8;a.mesh(root,new T.ConeGeometry(.10,h,5),M.blue,[j*.46,4.4-h/2,.76]).rotation.z=Math.PI;}
}
export function eyrie(a,p,K){const {M,spire,hall,arch}=K;p.userData.domain='mountain-eyrie';
 for(const [x,z,h,rx,rz]of [[-3.5,-8.5,3.8,1.8,2.0],[.2,-9.3,4.9,2.0,1.6],[3.5,-8.0,3.4,1.6,1.8],[-8.15,-5.5,1.6,.95,1.05]])rock(a,p,x,z,h,rx,rz,M.dark);
 for(const [x,z,h,r,base]of [[-3.5,-8.6,3.1,.61,3.3],[.2,-9.2,3.3,.86,4.2],[3.5,-8.1,3.0,.58,2.9],[-1.8,-10.3,2.6,.47,3.8]]){const t=spire(a,p,x,z,h,r);t.position.y=base;}
 const house=hall(a,p,.1,-8.1,5.4,1.5);house.position.y=3.1;
 // Narrow supported stone approaches echo the sheer-sided mountain fortress.
 for(const s of [-1,1]){for(let j=0;j<8;j++){const z=-5.6+j*1.22,y=.6+(7-j)*.18;a.box(p,[1.05,.22,1.26],[s*8.2,y,z],M.limestone);a.box(p,[.34,y,.46],[s*8.2,y/2,z],M.dark);for(const dx of [-.51,.51])a.box(p,[.09,.38,1.25],[s*8.2+dx,y+.26,z],M.limestone);}
  spire(a,p,s*8.15,-5.5,2.2,.5).position.y=1.7;
 }
 // Both side approaches reach the mountain hall instead of ending at isolated towers.
 stoneWalk(a,p,[-8.2,1.98,-5.6],[-6.7,2.55,-7.1],K);
 stoneWalk(a,p,[-6.7,2.55,-7.1],[-2.45,3.35,-8.1],K);
 stoneWalk(a,p,[8.2,1.98,-5.6],[6.7,2.5,-7.0],K);
 stoneWalk(a,p,[6.7,2.5,-7.0],[2.65,3.35,-8.1],K);
 stoneWalk(a,p,[8.2,.71,2.94],[7.8,.57,4.05],K);
 // Open moon-door rotunda, rather than another solid domed observatory.
 const court=new T.Group();court.position.set(7.8,.3,5.0);p.add(court);a.torus(court,1.2,.22,[0,.18,0],M.limestone);
 for(let j=0;j<8;j++){const q=j*Math.PI/4,facade=new T.Group();facade.rotation.y=q;court.add(facade);arch(a,facade,0,.4,1.1,.56,1.65,M.limestone,M.dark);a.cylinder(facade,.11,1.9,[.46,1.28,1.05],M.limestone);}a.torus(court,1.18,.15,[0,2.23,0],M.limestone);
}
export function movingKeep(a,p,K){const {M,group}=K,root=group(p,0,-10.75);root.userData.landmark='patchwork-moving-keep';
 const copper=new T.MeshStandardMaterial({color:0x885335,roughness:.66,metalness:.58}),rust=new T.MeshStandardMaterial({color:0x573b32,roughness:.83,metalness:.32});
 const body=a.mesh(root,new T.SphereGeometry(1,20,14),copper,[0,4.2,0]);body.scale.set(2.6,1.65,1.20);
 // Overlapping curved boiler plates and visible rows of rivets.
 for(let j=0;j<7;j++){const x=-2.1+j*.68;a.torus(root,.78,.045,[x,4.18,.48],M.gold,[0,Math.PI/2,0]);for(let k=0;k<5;k++)a.mesh(root,new T.SphereGeometry(.045,6,4),M.gold,[x,3.35+k*.36,1.02]);}
 for(const [x,y,h,r]of [[-1.7,5.1,2.6,.22],[-.8,5.5,2.0,.29],[.3,5.8,2.5,.18],[1.8,5.1,1.7,.27]]){a.cylinder(root,r,h,[x,y+h/2,-.15],rust);for(const yy of [y+.15,y+h-.1])a.torus(root,r*1.22,.07,[x,yy,-.15],copper);a.cylinder(root,r*.72,.05,[x,y+h+.015,-.15],M.dark);}
 const cabin=a.box(root,[1.65,1.1,1.3],[.65,6.0,.15],M.limestone);cabin.rotation.z=.08;
 for(const s of [-1,1]){const roof=a.box(root,[1.15,.12,1.65],[.65+s*.43,6.85,.15],M.slate);roof.rotation.z=-s*.55;for(const y of [3.55,4.5]){a.torus(root,.24,.09,[s*1.35,y,1.07],M.gold,[0,0,0]);a.cylinder(root,.16,.05,[s*1.35,y,1.09],M.window).rotation.x=Math.PI/2;}}
 for(const s of [-1,1]){const leg=group(root,s*1.8,.2);leg.position.y=2.6;a.rod(leg,[0,0,0],[s*.45,-1.0,.1],.13,rust);a.mesh(leg,new T.SphereGeometry(.22,10,8),M.gold,[s*.45,-1,.1]);a.rod(leg,[s*.45,-1,.1],[s*.70,-2.0,.3],.12,copper);a.box(leg,[.8,.20,.8],[s*.7,-2,.4],rust);jointMotion(a,leg,{axis:'z',amplitude:.065,speed:.65,phase:s*Math.PI/2});}
}
