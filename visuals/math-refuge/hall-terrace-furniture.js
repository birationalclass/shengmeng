import * as T from '../3d/vendor/three.module.js';
import {BUILDING_SCALE as S} from './site-layout.js';
export function createHallTerraceFurniture(scene,materials,offset){
 const root=new T.Group();root.name='Hall terrace B sea conversation';root.position.set(offset.x,.295*S,offset.z);scene.add(root);
 const wood=new T.MeshStandardMaterial({color:0x514338,roughness:.68,metalness:.02});
 const fabric=new T.MeshStandardMaterial({color:0xb5ad9b,roughness:.96,normalMap:materials.pale?.normalMap||null,normalScale:new T.Vector2(.16,.16)});
 const metal=new T.MeshStandardMaterial({color:0x39413f,roughness:.65,metalness:.3});
 const stone=materials.hallPaving||materials.stone,soil=materials.soil||metal;
 const batches=new Map(),matrix=new T.Matrix4(),q=new T.Quaternion(),unit=new T.BoxGeometry(),leafGeometry=new T.BufferGeometry();
 const leafColors=[0x4c5b40,0x61714b,0x74805a].map(color=>new T.MeshStandardMaterial({color,roughness:.91,side:T.DoubleSide}));
 const verts=[];
 for(let i=0;i<7;i++){
  const point=(t,side)=>[.48*t*t,Math.sin(t*Math.PI*.62),side*(.018*Math.sin(Math.PI*t)+.007*(1-t))];
  const a=point(i/7,-1),b=point(i/7,1),c=point((i+1)/7,-1),d=point((i+1)/7,1);verts.push(...a,...b,...c,...b,...d,...c);
 }
 leafGeometry.setAttribute('position',new T.Float32BufferAttribute(verts,3));leafGeometry.computeVertexNormals();
 function part(p,size,mat,yaw=0,geometry=unit){const key=mat.uuid+geometry.uuid;if(!batches.has(key))batches.set(key,{mat,geometry,items:[]});matrix.compose(new T.Vector3(...p),q.setFromAxisAngle(new T.Vector3(0,1,0),yaw),new T.Vector3(...size));batches.get(key).items.push(matrix.clone());}
 function chair(x,z,yaw){
  const item=new T.Object3D();item.name='Terrace timber armchair';item.position.set(x,0,z);item.userData={width:.76,depth:.78,height:.79};root.add(item);
  const add=(p,size,mat)=>{const c=Math.cos(yaw),s=Math.sin(yaw);part([x+p[0]*c+p[2]*s,p[1],z-p[0]*s+p[2]*c],size,mat,yaw);};
  for(const a of [-.31,.31])for(const b of [-.29,.29]){add([a,.225,b],[.055,.45,.055],wood);add([a,.02,b],[.058,.025,.058],metal);}
  for(const a of [-.33,.33]){add([a,.37,0],[.06,.10,.72],wood);add([a,.61,0],[.075,.05,.77],wood);for(const b of [-.27,.29])add([a,.50,b],[.045,.20,.045],wood);}
  for(const b of [-.32,.32])add([0,.37,b],[.61,.085,.05],wood);
  add([0,.437,-.01],[.58,.105,.60],fabric);add([0,.63,.31],[.59,.29,.09],fabric);
  add([0,.79,.35],[.72,.045,.055],wood);for(const a of [-.32,.32])add([a,.64,.35],[.045,.30,.055],wood);
  for(let i=0;i<5;i++)add([-.22+i*.11,.64,.375],[.027,.26,.025],wood);
 }
 function planter(x,z,w,d){
  part([x,.25,z],[w,.50,d],stone);part([x,.507,z],[w-.12,.02,d-.12],soil);
  const rows=Math.max(1,Math.floor(d/.32)),cols=Math.max(1,Math.floor(w/.32));
  for(let i=0;i<cols;i++)for(let j=0;j<rows;j++){
   const px=x-w/2+.17+(i+.5)*(w-.34)/cols,pz=z-d/2+.17+(j+.5)*(d-.34)/rows;
   for(let k=0;k<9;k++){const h=.28+.14*(.5+.5*Math.sin(i*11+j*7+k*3));part([px,.525,pz],[h,h,h],leafColors[(i+j+k)%3],k*2.399+i*.7+j*.3,leafGeometry);}
  }
 }
 for(const sign of [-1,1]){
  const x=49*S,z=sign*11*S,spacing=1.28;
  // Each chair faces the shared table. Keep all footprints within a 4.5 m square.
  for(const [dx,dz] of [[-spacing,0],[spacing,0],[0,-spacing],[0,spacing]])chair(x+dx,z+dz,Math.atan2(dx,dz));
  part([x,.18,z],[.68,.36,.68],metal);part([x,.385,z],[.94,.07,.94],stone);
  for(const dx of [-.48,.48])part([x+dx,.413,z],[.025,.016,.98],wood);
  for(const dz of [-.48,.48])part([x,.413,z+dz],[.94,.016,.025],wood);
  // Recessed perimeter joint defines the conversation area without a raised rug.
  for(const dx of [-2.25,2.25])part([x+dx,.007,z],[.018,.008,4.5],metal);
  for(const dz of [-2.25,2.25])part([x,.007,z+dz],[4.5,.008,.018],metal);
  planter(52.6*S,sign*4.7*S,.8,3.2);
 }
 const bx=47*S,bz=-14.1*S;
 for(let i=0;i<7;i++)part([bx,.465,bz-.29+i*.085],[4,.045,.069],wood);
 for(const dx of [-1.65,0,1.65])part([bx+dx,.225,bz],[.085,.43,.50],metal);
 part([bx,.39,bz],[3.85,.07,.47],wood);planter(bx,bz-.83,4,.65);
 for(const [x,z] of [[27,-14],[27,14],[52,-14],[52,14],[44,-15]]){
  part([x*S,.285,z*S],[.105,.57,.105],metal);part([x*S,.60,z*S],[.20,.075,.18],metal);
  part([x*S,.554,z*S],[.14,.012,.12],materials.terraceStrip||materials.light);
  part([x*S,.014,z*S],[.16,.028,.16],metal);
 }
 for(const {mat,geometry,items} of batches.values()){
  const mesh=new T.InstancedMesh(geometry,mat,items.length);items.forEach((m,i)=>mesh.setMatrixAt(i,m));mesh.castShadow=mat!==materials.terraceStrip;mesh.receiveShadow=true;mesh.computeBoundingSphere();root.add(mesh);
 }
 root.userData={scheme:'B',conversationGroups:2,chairs:8,tableSize:.98,readingBenchLength:4,minimumClearRoute:2.4};return root;
}
