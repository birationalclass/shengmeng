import {curvedDeck} from './bridge-deck.js?v=border-deck-44';
import * as T from '../3d/vendor/three.module.js';
import {BUILDING_SCALE as S} from './site-layout.js';

export function createSeaPavilion(scene,materials,offset){
 const root=new T.Group();root.name='Hall sea promenade and pavilion';scene.add(root);
 // Continue the western entrance canopy onto open water, bending north of the sunset axis.
 const origin=new T.Vector3(24*S+offset.x,.275*S,offset.z);
 root.position.copy(origin);
 const curve=new T.CatmullRomCurve3([[0,0,0],[-7,0,0],[-20,0,-7],[-36,0,-12]].map(p=>new T.Vector3(...p)));
 const batches=new Map(),matrix=new T.Matrix4(),q=new T.Quaternion(),up=new T.Vector3(0,1,0);
 const deck=materials.hallPaving||materials.terraceFloor||materials.stone;
 const steel=materials.steel,wood=new T.MeshStandardMaterial({color:0x493d32,roughness:.68,metalness:.03}),edge=materials.edge,brass=materials.brass;
 const roof=new T.MeshStandardMaterial({color:0x454d50,roughness:.87,metalness:.12});
 const frame=new T.MeshStandardMaterial({color:0x303736,roughness:.78,metalness:.12});
 const glow=new T.MeshStandardMaterial({color:0xc9ac78,emissive:0xffc680,emissiveIntensity:.45,roughness:.65});
 let pavilionTransform=null;
 function box(p,size,mat,yaw=0){
  if(pavilionTransform){const {x,z,angle}=pavilionTransform,dx=p[0]-x,dz=p[2]-z,c=Math.cos(angle),s=Math.sin(angle);p=[x+c*dx+s*dz,p[1],z-s*dx+c*dz];yaw+=angle;}
  if(!batches.has(mat))batches.set(mat,[]);
  q.setFromAxisAngle(up,yaw);matrix.compose(new T.Vector3(...p),q,new T.Vector3(...size));batches.get(mat).push(matrix.clone());
 }
 function beam(a,b,width,height,mat){const d=new T.Vector3().subVectors(b,a);box(a.clone().add(b).multiplyScalar(.5).toArray(),[width,height,d.length()+.012],mat,Math.atan2(d.x,d.z));}
 const flare=u=>{const t=Math.max(0,Math.min(1,u));return 3-2*t*t*t*(10-15*t+6*t*t);};
 const at=(u,side=0,y=0)=>{const p=curve.getPointAt(u),d=curve.getTangentAt(u);return p.add(new T.Vector3(-d.z,0,d.x).multiplyScalar(side*flare(u))).add(new T.Vector3(0,y,0));};
 const length=curve.getLength(),count=Math.ceil(length/.575);
 root.add(curvedDeck(curve,u=>2.8*flare(u),count,deck,1,.07));
 // Open timber boardwalk: all structure stays below the walking surface.
 for(let i=0;i<48;i++)for(const side of [-1,1]){
  beam(at(i/48,side*1.28,-.19),at((i+1)/48,side*1.28,-.19),.12,.27,steel);
  beam(at(i/48,side*1.42,-.075),at((i+1)/48,side*1.42,-.075),.055,.15,edge);
  beam(at(i/48,side*1.22,-.075),at((i+1)/48,side*1.22,-.075),.018,.015,glow);
 }
 const bays=Math.ceil(length/2.8);
 for(let i=0;i<=bays;i++){
  const u=i/bays;
  for(const side of [-1,1]){
   if(i%2===0){box(at(u,side*1.15,-2.8).toArray(),[.22,5.35,.22],steel);box(at(u,side*1.15,-.38).toArray(),[.34,.24,.34],edge);}
  }
 }
 const end=curve.getPointAt(1),tangent=curve.getTangentAt(1),cx=end.x-3.95,cz=end.z;
 // Align the pavilion's entrance normal with the arriving bridge tangent.
 pavilionTransform={x:end.x,z:end.z,angle:Math.atan2(tangent.z,-tangent.x)};
 box([cx,-.2,cz],[8,.32,7],edge);
 for(let i=0;i<6;i++)for(let j=0;j<6;j++)box([cx-4+(j+.5)*8/6,-.025,cz-3.5+(i+.5)*7/6],[8/6-.006,.05,7/6-.006],deck);
 for(const x of [-3.5,3.5])for(const z of [-3,3]){
  box([cx+x,1.48,cz+z],[.12,2.96,.12],frame);
  box([cx+x,.045,cz+z],[.27,.09,.27],brass);
  box([cx+x,-3,cz+z],[.3,5.6,.3],steel);
 }
 // Four gently swept roof faces, with individual tile courses and raised hip ridges.
 const tileShade=new T.MeshStandardMaterial({color:0x535a59,roughness:.92,metalness:.04});
 const ridgeMaterial=new T.MeshStandardMaterial({color:0x363f40,roughness:.78,metalness:.1});
 const local=(x,y,z)=>{
  const {x:ox,z:oz,angle}=pavilionTransform,c=Math.cos(angle),s=Math.sin(angle);
  return new T.Vector3(ox+c*(x-ox)+s*(z-oz),y,oz-s*(x-ox)+c*(z-oz));
 };
 const roofPoint=(side,u,v,dy=0)=>{
  const perimeter=[[u*4.65,-4.15],[4.65,u*4.15],[-u*4.65,4.15],[-4.65,-u*4.15]][side];
  const y=3.08+1.9*(1-v)*(1-v)+.24*Math.pow(v,6)+.57*Math.pow(Math.abs(u),8)*Math.pow(v,6);
  return local(cx+perimeter[0]*v,y+dy,cz+perimeter[1]*v);
 };
 const roofMesh=(dy,mat)=>{
  const points=[],uvs=[];
  for(let side=0;side<4;side++)for(let row=0;row<24;row++)for(let col=0;col<36;col++){
   const u=col/18-1,U=(col+1)/18-1,v=row/24,V=(row+1)/24;
   const corners=[roofPoint(side,u,v,dy),roofPoint(side,U,v,dy),roofPoint(side,U,V,dy),roofPoint(side,u,V,dy)];
   for(const i of [0,2,1,0,3,2]){points.push(...corners[i].toArray());uvs.push(corners[i].x*.4,corners[i].z*.4);}
  }
  const g=new T.BufferGeometry();g.setAttribute('position',new T.Float32BufferAttribute(points,3));g.setAttribute('uv',new T.Float32BufferAttribute(uvs,2));g.computeVertexNormals();
  const m=new T.Mesh(g,mat);m.name=dy?'Pavilion swept timber soffit':'Pavilion four swept tiled roof faces';m.castShadow=m.receiveShadow=true;root.add(m);
 };
 roof.side=T.DoubleSide;frame.side=T.DoubleSide;roofMesh(0,roof);roofMesh(-.11,frame);
 function molding(points,radius,mat,name){
  const path=new T.CatmullRomCurve3(points),mesh=new T.Mesh(new T.TubeGeometry(path,Math.max(12,points.length*2),radius,6,false),mat);
  mesh.name=name;mesh.castShadow=mesh.receiveShadow=true;root.add(mesh);
 }
 for(let side=0;side<4;side++){
  for(let row=3;row<=24;row++){
   const v=row/24,points=Array.from({length:37},(_,j)=>roofPoint(side,j/18-1,v,.014));
   molding(points,.017,tileShade,'Pavilion overlapping tile course');
  }
  for(let col=0;col<=36;col++){
   const u=col/18-1,points=Array.from({length:23},(_,j)=>roofPoint(side,u,.09+.91*j/22,.027));
   molding(points,.025,col%2?roof:tileShade,'Pavilion rounded tile channel');
  }
  molding(Array.from({length:25},(_,j)=>roofPoint(side,1,j/24,.065)),.075,ridgeMaterial,'Pavilion raised sweeping hip ridge');
  molding(Array.from({length:37},(_,j)=>roofPoint(side,j/18-1,1,-.035)),.065,ridgeMaterial,'Pavilion curved eave fascia');
 }
 const peak=local(cx,5.08,cz);
 const finial=new T.Mesh(new T.LatheGeometry([new T.Vector2(.12,0),new T.Vector2(.18,.07),new T.Vector2(.14,.15),new T.Vector2(.08,.24),new T.Vector2(.065,.36),new T.Vector2(0,.54)],24),ridgeMaterial);finial.position.copy(peak);finial.name='Pavilion roof finial';finial.castShadow=true;root.add(finial);
 // Visible structural load path: roof > curved rafters > purlins > column capitals.
 for(let side=0;side<4;side++){
  for(let rib=0;rib<=16;rib++)molding(Array.from({length:19},(_,j)=>roofPoint(side,rib/8-1,.18+.82*j/18,-.18)),.052,wood,'Pavilion swept timber rafter');
  for(const v of [.38,.73,.9])molding(Array.from({length:25},(_,j)=>roofPoint(side,j/12-1,v,-.24)),.085,wood,'Pavilion continuous supporting purlin');
 }
 for(const z of [-3,3])box([cx,3.075,cz+z],[7.25,.30,.22],wood);
 for(const x of [-3.5,3.5])box([cx+x,3.075,cz],[.22,.30,6.2],wood);
 for(const x of [-3.5,3.5])for(const z of [-3,3]){
  box([cx+x,3.015,cz+z],[.24,.5,.24],wood);
  box([cx+x,3.16,cz+z],[.72,.14,.34],wood);
  box([cx+x,3.19,cz+z],[.34,.14,.72],wood);
 }
 // A continuous timber frame and restrained brackets under the overhanging roof.
 for(const z of [-3,3]){box([cx,2.84,cz+z],[7.25,.24,.16],frame);box([cx,2.56,cz+z],[7.1,.09,.1],frame);}
 for(const x of [-3.5,3.5]){box([cx+x,2.84,cz],[.16,.24,6.2],frame);box([cx+x,2.56,cz],[.1,.09,6.1],frame);}
 for(const x of [-3.5,3.5])for(const z of [-3,3]){
  box([cx+x,.12,cz+z],[.42,.24,.42],deck);
  box([cx+x,.27,cz+z],[.27,.07,.27],ridgeMaterial);
  box([cx+x,1.55,cz+z],[.19,2.6,.19],frame);
  for(let j=0;j<3;j++){
   box([cx+x,2.61+j*.1,cz+z],[.34+j*.2,.085,.24],frame);
   box([cx+x,2.65+j*.1,cz+z],[.24,.075,.34+j*.2],frame);
  }
 }
 for(let i=0;i<20;i++)for(const z of [-3,3])box([cx-3.25+i*6.5/19,2.69,cz+z],[.035,.2,.055],frame);
 for(let i=0;i<16;i++)for(const x of [-3.5,3.5])box([cx+x,2.69,cz-2.75+i*5.5/15],[.055,.2,.035],frame);
 // Framed dark-wood benches: low lattice back, recessed seat panels and mortise-like legs.
 for(const sign of [-1,1]){
  const z=cz+sign*2.65,back=z+sign*.33;
  for(const dz of [-.30,.30])box([cx,.43,z+dz],[5.8,.12,.085],wood);
  for(let j=0;j<12;j++)box([cx-2.65+j*5.3/11,.482,z],[.46,.04,.50],wood);
  for(const x of [-2.8,0,2.8]){
   box([cx+x,.23,z-.23],[.11,.44,.11],wood);box([cx+x,.23,z+.23],[.11,.44,.11],wood);
   box([cx+x,.69,back],[.09,.62,.09],wood);
  }
  box([cx,.94,back],[5.86,.09,.11],wood);box([cx,.60,back],[5.7,.065,.075],wood);
  for(let j=0;j<17;j++)box([cx-2.64+j*.33,.77,back],[.035,.28,.045],wood);
  box([cx,.27,z-sign*.23],[5.5,.09,.065],wood);
  for(const x of [-2.82,2.82]){
   box([cx+x,.70,z],[.075,.08,.69],wood);
   box([cx+x,.59,z-sign*.28],[.065,.25,.065],wood);
  }
  box([cx,2.97,cz+sign*2.88],[6,.016,.025],glow);
 }
 // A low square tea table with inset stone centre, apron and four timber legs.
 box([cx,.53,cz],[1.3,.075,.95],wood);box([cx,.573,cz],[1.12,.012,.77],deck);
 for(const x of [-.51,.51])for(const z of [-.34,.34])box([cx+x,.265,cz+z],[.075,.5,.075],wood);
 for(const z of [-.36,.36])box([cx,.44,cz+z],[1.08,.13,.055],wood);
 for(const x of [-.53,.53])box([cx+x,.44,cz],[.055,.13,.72],wood);
 // Merge repeated roof tiles by material to keep the detailed roof inexpensive to draw.
 const details=new Map();
 for(const mesh of [...root.children])if(mesh.name.startsWith('Pavilion ')){
  mesh.updateMatrix();const g=mesh.geometry.clone().applyMatrix4(mesh.matrix),flat=g.index?g.toNonIndexed():g;
  if(!details.has(mesh.material))details.set(mesh.material,[]);details.get(mesh.material).push(flat);
  if(flat!==g)g.dispose();mesh.geometry.dispose();root.remove(mesh);
 }
 for(const [mat,geometries] of details){
  const merged=new T.BufferGeometry();
  for(const key of ['position','normal','uv']){
   const size=key==='uv'?2:3,total=geometries.reduce((n,g)=>n+g.attributes[key].array.length,0),array=new Float32Array(total);let start=0;
   for(const g of geometries){array.set(g.attributes[key].array,start);start+=g.attributes[key].array.length;}
   merged.setAttribute(key,new T.BufferAttribute(array,size));
  }
  geometries.forEach(g=>g.dispose());merged.computeBoundingSphere();const mesh=new T.Mesh(merged,mat);mesh.name='Pavilion merged roof detail';mesh.castShadow=mesh.receiveShadow=true;root.add(mesh);
 }
 for(const [mat,transforms] of batches){
  const mesh=new T.InstancedMesh(new T.BoxGeometry(1,1,1),mat,transforms.length);
  transforms.forEach((m,i)=>mesh.setMatrixAt(i,m));mesh.castShadow=mat!==glow;mesh.receiveShadow=true;
  mesh.name='Sea pavilion '+(mat===roof?'grey tiled roof':mat===frame?'charcoal columns':mat===wood?'timber details':'structure');mesh.computeBoundingSphere();root.add(mesh);
 }
 root.userData.dimensions={bridgeLength:length,bridgeWidth:2.8,entranceWidth:8.4,pavilion:[8,7]};
 return {root,position:new T.Vector3(end.x+tangent.x*3.95,0,end.z+tangent.z*3.95).add(origin)};
}
