import * as T from '../3d/vendor/three.module.js';
import {BUILDING_SCALE as S} from './site-layout.js';

export function createSeaPavilion(scene,materials,offset){
 const root=new T.Group();root.name='Hall sea promenade and pavilion';scene.add(root);
 // Continue the western entrance canopy onto open water, bending north of the sunset axis.
 const origin=new T.Vector3(24*S+offset.x,.275*S,offset.z);
 root.position.copy(origin);
 const curve=new T.CatmullRomCurve3([[0,0,0],[-7,0,0],[-20,0,-7],[-36,0,-12]].map(p=>new T.Vector3(...p)));
 const batches=new Map(),matrix=new T.Matrix4(),q=new T.Quaternion(),up=new T.Vector3(0,1,0);
 const steel=materials.steel,wood=materials.timber,edge=materials.edge,brass=materials.brass;
 const glow=new T.MeshStandardMaterial({color:0xc9ac78,emissive:0xffc680,emissiveIntensity:.45,roughness:.65});
 const glass=materials.glass.clone();glass.opacity=.13;glass.depthWrite=false;
 function box(p,size,mat,yaw=0){
  if(!batches.has(mat))batches.set(mat,[]);
  q.setFromAxisAngle(up,yaw);matrix.compose(new T.Vector3(...p),q,new T.Vector3(...size));batches.get(mat).push(matrix.clone());
 }
 function beam(a,b,width,height,mat){const d=new T.Vector3().subVectors(b,a);box(a.clone().add(b).multiplyScalar(.5).toArray(),[width,height,d.length()+.012],mat,Math.atan2(d.x,d.z));}
 const at=(u,side=0,y=0)=>{const p=curve.getPointAt(u),d=curve.getTangentAt(u);return p.add(new T.Vector3(-d.z,0,d.x).multiplyScalar(side)).add(new T.Vector3(0,y,0));};
 const length=curve.getLength(),count=Math.ceil(length/.155);
 for(let i=0;i<count;i++){
  const u=(i+.5)/count,d=curve.getTangentAt(u);
  box(at(u,0,-.035).toArray(),[2.8,.07,length/count-.005],wood,Math.atan2(d.x,d.z));
 }
 // Concealed stringers, edge fascia, slim continuous rails and covered walkway.
 for(let i=0;i<48;i++)for(const side of [-1,1]){
  beam(at(i/48,side*1.28,-.19),at((i+1)/48,side*1.28,-.19),.12,.27,steel);
  beam(at(i/48,side*1.42,-.075),at((i+1)/48,side*1.42,-.075),.055,.15,edge);
  beam(at(i/48,side*1.39,1.08),at((i+1)/48,side*1.39,1.08),.048,.045,brass);
  beam(at(i/48,side*1.55,2.85),at((i+1)/48,side*1.55,2.85),.085,.18,steel);
  beam(at(i/48,side*1.22,-.075),at((i+1)/48,side*1.22,-.075),.018,.015,glow);
 }
 const bays=Math.ceil(length/2.8);
 for(let i=0;i<=bays;i++){
  const u=i/bays,d=curve.getTangentAt(u),yaw=Math.atan2(d.x,d.z);
  for(const side of [-1,1]){
   box(at(u,side*1.39,.53).toArray(),[.045,1.06,.045],steel);
   box(at(u,side*1.39,.025).toArray(),[.15,.05,.15],steel);
   box(at(u,side*1.53,1.4).toArray(),[.075,2.8,.075],steel);
   if(i%2===0){box(at(u,side*1.15,-2.8).toArray(),[.22,5.35,.22],steel);box(at(u,side*1.15,-.38).toArray(),[.34,.24,.34],edge);}
  }
  box(at(u,0,2.83).toArray(),[3.25,.1,.075],steel,yaw);
  if(i<bays)for(const side of [-1,1]){
   beam(at(u,side*1.39,.56),at((i+1)/bays,side*1.39,.56),.013,.94,glass);
  }
 }
 for(let i=0;i<Math.ceil(length/.28);i++){
  const u=(i+.5)/Math.ceil(length/.28),d=curve.getTangentAt(u);
  box(at(u,0,2.94).toArray(),[3.28,.065,.08],wood,Math.atan2(d.x,d.z));
 }
 // Weather roof above the timber soffit: narrow panels follow the bridge's curve.
 for(let i=0;i<48;i++){const u=(i+.5)/48,d=curve.getTangentAt(u);box(at(u,0,3.03).toArray(),[3.38,.07,length/48+.025],edge,Math.atan2(d.x,d.z));}
 const end=curve.getPointAt(1),cx=end.x-3.95,cz=end.z;
 box([cx,-.2,cz],[8,.32,7],edge);
 for(let i=0;i<46;i++)box([cx,-.025,cz-3.5+(i+.5)*7/46],[7.98,.05,7/46-.004],wood);
 for(const x of [-3.5,3.5])for(const z of [-3,3]){
  box([cx+x,1.48,cz+z],[.12,2.96,.12],steel);
  box([cx+x,.045,cz+z],[.27,.09,.27],brass);
  box([cx+x,-3,cz+z],[.3,5.6,.3],steel);
 }
 box([cx,3.17,cz],[8.8,.16,7.8],edge);
 box([cx,3.04,cz],[8.3,.09,7.3],wood);
 for(let i=0;i<36;i++)box([cx-4.05+i*8.1/35,2.95,cz],[.065,.11,7.2],wood);
 for(const z of [-3.42,3.42]){
  box([cx,.56,cz+z],[7.8,.94,.014],glass);
  box([cx,1.08,cz+z],[8,.045,.048],brass);
  for(const x of [-3.9,-1.3,1.3,3.9])box([cx+x,.53,cz+z],[.045,1.06,.045],steel);
  // Floating timber benches, recessed supports and slatted backrest.
  box([cx,.44,cz+z*.79],[5.8,.085,.62],wood);
  for(const x of [-2.3,2.3])box([cx+x,.21,cz+z*.79],[.075,.42,.43],steel);
  for(let i=0;i<3;i++)box([cx,.65+i*.1,cz+z*.9],[5.8,.065,.045],wood);
  box([cx,2.96,cz+z*.88],[6,.016,.025],glow);
 }
 // Ocean-facing rail; the east entry remains completely open to the bridge.
 for(const [z,d] of [[0,7]]){box([cx-3.92,.56,cz+z],[.014,.94,d-.2],glass);box([cx-3.92,1.08,cz+z],[.048,.045,d],brass);}
 for(const z of [-3.4,-1.1,1.1,3.4])box([cx-3.92,.53,cz+z],[.045,1.06,.045],steel);
 for(const side of [-1,1]){box([cx+3.92,.56,cz+side*2.45],[.014,.94,2.0],glass);box([cx+3.92,1.08,cz+side*2.45],[.048,.045,2.0],brass);}
 box([cx,.56,cz],[1.3,.08,.85],wood);box([cx,.27,cz],[.12,.54,.12],steel);
 for(const [mat,transforms] of batches){
  const mesh=new T.InstancedMesh(new T.BoxGeometry(1,1,1),mat,transforms.length);
  transforms.forEach((m,i)=>mesh.setMatrixAt(i,m));mesh.castShadow=mat!==glass&&mat!==glow;mesh.receiveShadow=mat!==glass;
  mesh.name='Sea pavilion '+(mat===glass?'glass':mat===wood?'timber details':'structure');mesh.computeBoundingSphere();root.add(mesh);
 }
 root.userData.dimensions={bridgeLength:length,bridgeWidth:2.8,pavilion:[8,7]};
 return {root,position:new T.Vector3(cx,0,cz).add(origin)};
}
