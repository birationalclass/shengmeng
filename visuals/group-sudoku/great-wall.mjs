import {installWallBeacon} from './board-beacons.mjs?v=wall-gate2';
import * as T from '../3d/vendor/three.module.js';
import {jointMotion} from './architectural-motion.mjs?v=living1';

export function banner(a,parent,x,y,z,phase=0){
 const mast=new T.Group();mast.position.set(x,y,z);parent.add(mast);
 a.rod(mast,[0,0,0],[0,1.55,0],.035,a.materials.brass);
 a.mesh(mast,new T.SphereGeometry(.085,8,6),a.materials.gold,[0,1.57,0]);
 const fabric=a.materials.red.clone();fabric.side=T.DoubleSide;
 let previous= new T.Group();mast.add(previous);previous.position.y=1.30;
 for(let i=0;i<5;i++){
  const fold=new T.Group();previous.add(fold);fold.position.x=i===0?0:.17;
  a.mesh(fold,new T.PlaneGeometry(.18,.44-i*.035),fabric,[.085,-.16,0]);
  jointMotion(a,fold,{axis:'y',speed:1.8,amplitude:.22,phase:phase-i*.65});previous=fold;
 }
 return mast;
}

function autumnRandom(){let seed=913729;return ()=>((seed=(Math.imul(seed,1664525)+1013904223)>>>0)/4294967296);}
export function courtyardTreePositions(){
 const rand=autumnRandom(),points=[];
 for(let attempt=0;points.length<29&&attempt<6000;attempt++){
  const q=rand()*Math.PI*2,r=7.8+rand()*1.95,x=Math.sin(q)*r,z=-Math.cos(q)*r;
  if(Math.max(Math.abs(x),Math.abs(z))<6.92||z>5.9&&Math.abs(x)<2.0||points.some(p=>Math.hypot(x-p.x,z-p.z)<1.12))continue;
  points.push({x,z,height:1.04+rand()*.45+(1-z/10)*.32,scale:.84+rand()*.20,phase:rand()*Math.PI*2});
 }
 return points;
}
function courtyardTrees(a,parent){
 const bark=new T.MeshStandardMaterial({color:0xc7bfa4,roughness:.95}),patch=new T.MeshStandardMaterial({color:0x887c61,roughness:1});
 const leaves=[0xe3b637,0xf2cc60,0xd99b29,0xc68b2a].map(color=>new T.MeshStandardMaterial({color,roughness:.94}));
 const crownGeometry=new T.SphereGeometry(1,8,6),trunkGeometry=new T.CylinderGeometry(.085,.14,1,7);
 courtyardTreePositions().forEach(({x,z,height:h,scale,phase},i)=>{
  const tree=new T.Group();tree.userData.landmark='wutong-tree';tree.position.set(x,.15,z);parent.add(tree);
  const trunk=a.mesh(tree,trunkGeometry,bark,[0,h*.48,0]);trunk.scale.y=h;
  for(let j=0;j<5;j++){const angle=j*2.4+i;const mark=a.mesh(tree,new T.SphereGeometry(.06,5,4),patch,[Math.sin(angle)*.11,.18+j*h*.14,Math.cos(angle)*.11]);mark.scale.set(.8,1.8,.45);mark.rotation.y=angle;}
  for(let j=0;j<3;j++){
   const angle=j*Math.PI*2/3+phase,dx=Math.sin(angle)*.28,dz=Math.cos(angle)*.28;
   a.rod(tree,[0,h*.60,0],[dx,h+.10,dz],.045,bark);
   const crown=a.mesh(tree,crownGeometry,leaves[(i+j)%4],[dx,h+.15+(j===0?.16:0),dz]);crown.scale.set(.51*scale,.39*scale,.51*scale);crown.rotation.y=angle;
  }
 });
}
function autumnLeafFloor(parent){
 const root=new T.Group();root.userData.landmark='autumn-leaf-floor';parent.add(root);
 const area=new T.Shape();area.absarc(0,0,10.72,0,Math.PI*2,false);const hole=new T.Path();hole.moveTo(-6.04,-6.04);hole.lineTo(-6.04,6.04);hole.lineTo(6.04,6.04);hole.lineTo(6.04,-6.04);hole.closePath();area.holes.push(hole);
 const bed=new T.Mesh(new T.ShapeGeometry(area,96),new T.MeshStandardMaterial({color:0xac7b32,roughness:1}));bed.rotation.x=-Math.PI/2;bed.position.y=.17;root.add(bed);
 // Five-lobed fallen leaves, shared as one instanced mesh with varied colors,
 // rotations and small height offsets rather than a tiled floor texture.
 const leaf=new T.Shape();const outline=[[0,1],[.18,.43],[.65,.62],[.47,.12],[1,.04],[.42,-.25],[.51,-.58],[.12,-.44],[0,-.79],[-.12,-.44],[-.51,-.58],[-.42,-.25],[-1,.04],[-.47,.12],[-.65,.62],[-.18,.43]];
 outline.forEach(([x,y],i)=>i?leaf.lineTo(x,y):leaf.moveTo(x,y));leaf.closePath();const geometry=new T.ShapeGeometry(leaf);geometry.rotateX(-Math.PI/2);
 const count=14000,mesh=new T.InstancedMesh(geometry,new T.MeshStandardMaterial({roughness:1,side:T.DoubleSide}),count),rand=autumnRandom(),dummy=new T.Object3D(),palette=[0xe9b944,0xf2ce6d,0xce9230,0xbb7627,0xd6a446,0x93602b].map(c=>new T.Color(c));
 for(let i=0;i<count;i++){
  let x,z;do{x=(rand()-.5)*21.3;z=(rand()-.5)*21.3;}while(Math.hypot(x,z)>10.59||Math.max(Math.abs(x),Math.abs(z))<6.21);
  const size=.09+rand()*.12;dummy.position.set(x,.19+rand()*.045,z);dummy.rotation.set((rand()-.5)*.10,rand()*Math.PI*2,(rand()-.5)*.10);dummy.scale.set(size,1,size*(.75+rand()*.55));dummy.updateMatrix();mesh.setMatrixAt(i,dummy.matrix);mesh.setColorAt(i,palette[Math.floor(rand()*palette.length)]);
 }
 mesh.computeBoundingSphere();root.add(mesh);
}

export function greatWall(a,parent){
 a.wallBeacons=[];const wall=new T.Group();wall.name='Great Wall · 万里长城';wall.userData.landmark='great-wall';parent.add(wall);
 const stone=a.materials.stone.clone();stone.color.setHex(0x9b947d);
 const cap=a.materials.paper.clone();cap.color.setHex(0xb8ad91);
 const mortar=a.materials.dark.clone();mortar.color.setHex(0x645f50);
 const at=q=>{const radius=11.35+.12*Math.cos(q*8);return new T.Vector3(Math.sin(q)*radius,0,-Math.cos(q)*radius);};
 // The southern gateway replaces four wall sections with a genuinely open passage.
 for(let i=0;i<64;i++){
  if(i>=30&&i<=33)continue;
  const q0=i*Math.PI*2/64,q1=(i+1)*Math.PI*2/64,p=at(q0),r=at(q1),d=r.clone().sub(p),len=d.length()+.045;
  const h=.55+2.00*(1+Math.cos((q0+q1)/2))/2;
  const segment=new T.Group();segment.userData.wallSegment={start:q0,end:q1,height:h};segment.position.copy(p.add(r).multiplyScalar(.5));segment.rotation.y=Math.atan2(d.x,d.z);wall.add(segment);
  a.box(segment,[1.03,h,len],[0,h/2+.15,0],stone);
  a.box(segment,[1.14,.12,len],[0,h+.20,0],cap);
  for(const side of [-1,1]){
   a.box(segment,[.16,.46,len],[side*.57,h+.48,0],stone);
   for(const z of [-len*.32,len*.32])a.box(segment,[.22,.34,.22],[side*.57,h+.88,z],cap);
   for(let row=0;row<Math.max(1,Math.floor(h/.37));row++){
    const y=.38+row*.37;a.box(segment,[.012,.015,len-.02],[side*.52,y,0],mortar);
    a.box(segment,[.012,.32,.018],[side*.525,y+.18,(row%2?1:-1)*len*.22],mortar);
   }
  }
  // Stone treads make the changing walkway height read as a walkable ramp.
  for(const z of [-len*.25,len*.25])a.box(segment,[.88,.022,.026],[0,h+.275,z],mortar);
 }
 for(const [j,q] of Array.from({length:8},(_,i)=>i*Math.PI/4).entries()){
  const p=at(q),tower=new T.Group();tower.position.copy(p);tower.rotation.y=-q;wall.add(tower);
  tower.userData.landmark=j===4?'great-wall-gateway':'great-wall-watchtower';
  if(j===4){
   // No foundation, wall or painted door crosses the 3.0-wide opening.
   for(const x of [-1.85,1.85]){
    a.box(tower,[.72,2.0,1.6],[x,1.15,0],stone);
    a.box(tower,[.84,.20,1.75],[x,.25,0],cap);
    for(let y=.55;y<2.1;y+=.38)a.box(tower,[.73,.018,1.61],[x,y,0],mortar);
   }
   a.box(tower,[4.5,.32,1.7],[0,2.30,0],stone);
   a.box(tower,[4.65,.13,1.85],[0,2.52,0],cap);
   for(const z of [-.82,.82])for(let k=-5;k<=5;k++)a.box(tower,[.27,.36,.20],[k*.40,2.77,z],cap);
   installWallBeacon(a,tower,2.60,j);continue;
  }
  const h=1.20+2.20*(1+Math.cos(q))/2,w=1.45;
  a.box(tower,[w+.3,.25,w+.3],[0,.25,0],cap);
  a.box(tower,[w,h,w],[0,h/2+.35,0],stone);
  for(let y=.7;y<h+.2;y+=.43)for(const side of [-1,1]){
   a.box(tower,[w,.018,.014],[0,y,side*(w/2+.008)],mortar);
   a.box(tower,[.014,.018,w],[side*(w/2+.008),y,0],mortar);
  }
  for(const side of [-1,1])for(const x of [-.43,.43]){
   a.box(tower,[.20,.51,.022],[x,h-.42,side*(w/2+.018)],a.materials.dark);
   a.box(tower,[.30,.08,.06],[x,h-.73,side*(w/2+.05)],cap);
  }
  a.box(tower,[w+.28,.16,w+.28],[0,h+.42,0],cap);
  for(const side of [-1,1]){
   a.box(tower,[w+.16,.35,.15],[0,h+.65,side*(w/2+.04)],stone);
   a.box(tower,[.15,.35,w+.16],[side*(w/2+.04),h+.65,0],stone);
   for(const x of [-.62,-.21,.21,.62]){
    a.box(tower,[.27,.32,.23],[x,h+.97,side*(w/2+.04)],cap);
    a.box(tower,[.23,.32,.27],[side*(w/2+.04),h+.97,x],cap);
   }
  }
  // Dark recessed doorway with stone jambs, instead of a solid painted door.
  a.box(tower,[.55,1.02,.03],[0,.87,w/2+.02],a.materials.dark);
  for(const x of [-.35,.35])a.box(tower,[.13,1.1,.12],[x,.91,w/2+.07],cap);
  a.box(tower,[.83,.15,.15],[0,1.49,w/2+.07],cap);
  installWallBeacon(a,tower,h+.55,j);
 }
 courtyardTrees(a,wall);
 autumnLeafFloor(parent);
 return wall;
}
