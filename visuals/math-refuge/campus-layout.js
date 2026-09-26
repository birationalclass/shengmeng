import {createSeaPavilion} from './sea-pavilion.js?v=pavilion-clean-22';
import {createHallSpiral} from './hall-spiral.js';
import {createRoofNumber} from './roof-number.js?v=campus-labels';
import * as T from 'three';
import {BUILDING_SCALE as S,HALL,LECTERN_SHAFT_PLAN} from './site-layout.js';
import {subtractRect} from './board-storage.js?v124';
import {createLecternLift} from './lectern-lift.js';
import {bridgePlan} from './campus-plan.js';
import {routeBridge} from './campus-routing.js';

const anchor=39*S;
export const members=new Map(),sharedVertices=[];
function track(object,id){if(!members.has(id))members.set(id,new Set());members.get(id).add(object);object.userData.layoutId=id;return object;}
// [drawing ID, name, old centre X/Z in plan units, proposed centre E/N in metres, platform W/D].
export const layout=[
 ['01B','报告厅',39,0,-62,0,30*S,33*S],
 ['02','图书馆',-37,-16,-185,295,32,24],
 ['03','共研工坊',-6,-4,-175,175,30,28],
 ['04','数学实验室',11.5,-4,-180,-170,30,24],
 ['05N','北食阁',39,-22,-103,171,30,24],
 ['05S','南食阁',-36.5,19,-103,-166,30,24],
 ['07','教学楼',-84,8,-185,-235,36,30],
 ['R1','休息室一组',-56,-28,-103,95,26,20],
 ['R3','休息室三组',-47,-38,-122,-110,26,20],
 ['G','海上花园',-43,0,-250,320,55,80],
 ['01C','报告厅固定备份',39,0,-103,225,30*S,33*S],
 ['06','访客小院',-56,-28,-186,355,36,28],
 ['R2','休息室二组',-47,-38,-175,235,26,20]
];
const byId=id=>layout.find(b=>b[0]===id);
function owner(x,z){
 if(x>23&&z>=-16.6&&z<=16.6)return byId('01B');
 if(x>30&&z< -16.6)return byId('05N');
 if(x< -75)return byId('07');
 if(x>=-62&&x<=-48&&z>=-34&&z<=-22)return byId('R1');
 if(x>=-53&&x<=-41&&z>=-44&&z<=-32)return byId('R3');
 if(x>=-45&&x<=-29&&z>=-23&&z<=-9)return byId('02');
 if(x>=-44&&x<=-29&&z>=13&&z<=25)return byId('05S');
 if(x>=-24&&x<=2&&z>=-26&&z<=26)return byId('03');
 if(x>=5&&x<=19&&z>=-26&&z<=26)return byId('04');
 return byId('G');
}
const offset=b=>new T.Vector3(anchor+b[4]-b[2]*S,0,-b[5]-b[3]*S);
const relocation=b=>{
 const sx=b[0]==='G'?.7:1,sz=b[0]==='G'?.55:1;
 return new T.Matrix4().makeTranslation(anchor+b[4],0,-b[5]).multiply(new T.Matrix4().makeScale(sx,1,sz)).multiply(new T.Matrix4().makeTranslation(-b[2]*S,0,-b[3]*S));
};
const destinations=b=>[b,...(b[0]==='01B'?[byId('01C')]:b[0]==='R1'?[byId('06')]:b[0]==='R3'?[byId('R2')]:[])];
export function relocateArchitecture(scene,objects,worldInstances=false){
 scene.updateMatrixWorld(true);
 const scratch=new T.Matrix4(),point=new T.Vector3();
 for(const obj of [...objects]){
  // Ground plates are replaced with the drawing's independent platform envelopes.
  if(obj.name.startsWith('Unified platform')){
   if(obj.name.endsWith(' 0')){obj.visible=false;continue;}
   const geom=(obj.geometry.index?obj.geometry.toNonIndexed():obj.geometry.clone()),pos=geom.attributes.position;
   const indices=new Map();
   for(let i=0;i<pos.count;i+=3){
    point.set(0,0,0);for(let j=0;j<3;j++)point.add(new T.Vector3().fromBufferAttribute(pos,i+j));point.divideScalar(3);
    const b=owner(point.x,point.z),delta=offset(b).divideScalar(S);
    if(!indices.has(b[0]))indices.set(b[0],[]);indices.get(b[0]).push(i,i+1,i+2);
    for(let j=0;j<3;j++)pos.setXYZ(i+j,pos.getX(i+j)+delta.x,pos.getY(i+j),pos.getZ(i+j)+delta.z);
   }
   geom.computeBoundingBox();geom.computeBoundingSphere();obj.geometry=geom;
   for(const [id,list] of indices)sharedVertices.push({id,geometry:geom,indices:list,scale:S});
   // Upper-floor and roof slabs for the exact hall duplicate.
   const src=obj.geometry.attributes.position,uv=obj.geometry.attributes.uv,verts=[],uvs=[];
   for(let i=0;i<src.count;i+=3){const x=(src.getX(i)+src.getX(i+1)+src.getX(i+2))/3,z=(src.getZ(i)+src.getZ(i+1)+src.getZ(i+2))/3;
    if(Math.abs(x*S-(anchor-62))<24&&Math.abs(z*S)<25)for(let j=0;j<3;j++){verts.push(src.getX(i+j)-41/S,src.getY(i+j),src.getZ(i+j)-225/S);if(uv)uvs.push(uv.getX(i+j),uv.getY(i+j));}
   }
   if(verts.length){const g=new T.BufferGeometry();g.setAttribute('position',new T.Float32BufferAttribute(verts,3));if(uvs.length)g.setAttribute('uv',new T.Float32BufferAttribute(uvs,2));g.computeVertexNormals();const m=new T.Mesh(g,obj.material);m.scale.copy(obj.scale);m.castShadow=m.receiveShadow=true;scene.add(track(m,'01C'));}
   continue;
  }
  if(obj.isInstancedMesh){
   const chunks=new Map();
   for(let i=0;i<obj.count;i++){
    obj.getMatrixAt(i,scratch);point.setFromMatrixPosition(scratch);
    const b=owner(point.x/(worldInstances?S:1),point.z/(worldInstances?S:1));
    for(const dest of destinations(b)){if(dest[0]==='01B'&&['original-hall-stair','hall-upper-edge-strip','removed-hall-west-canopy'].includes(obj.userData.campusParts?.[i]))continue;const unit=worldInstances?1:S;const transform=new T.Matrix4().makeScale(1/unit,1/unit,1/unit).multiply(relocation(dest)).multiply(new T.Matrix4().makeScale(unit,unit,unit));const matrix=scratch.clone().premultiply(transform);if(!chunks.has(dest[0]))chunks.set(dest[0],[]);matrix.designGroup=obj.userData.designGroups?.[i]||'';chunks.get(dest[0]).push(matrix);}
   }
   obj.visible=false;
   for(const [id,matrices] of chunks){const m=new T.InstancedMesh(obj.geometry,obj.material,matrices.length);m.name='Layout '+id+' '+obj.name;m.userData.designGroups=matrices.map(a=>a.designGroup);m.scale.copy(obj.scale);m.position.copy(obj.position);matrices.forEach((a,i)=>m.setMatrixAt(i,a));m.castShadow=obj.castShadow;m.receiveShadow=obj.receiveShadow;m.computeBoundingSphere();m.computeBoundingBox();scene.add(track(m,id));}
   continue;
  }
  if(/roof.*number/i.test(obj.name)){obj.visible=false;continue;}
  const bounds=new T.Box3().setFromObject(obj);
  if(bounds.isEmpty())continue;
  bounds.getCenter(point).divideScalar(S);const b=owner(point.x,point.z);
  for(const dest of destinations(b).slice(1)){const copy=obj.clone(true);copy.position.add(offset(dest));copy.name='Layout '+dest[0]+' '+obj.name;scene.add(track(copy,dest[0]));}
  obj.applyMatrix4(relocation(b));track(obj,b[0]);
 }
 scene.updateMatrixWorld(true);
}

export const campusLayout=layout.map(b=>{const r=bridgePlan.buildings.find(r=>r.id===b[0]);return [...b.slice(0,4),r.east,r.north,b[6],b[7]];});
export const buildingOffset=id=>offset(campusLayout.find(b=>b[0]===id));
export function finishCampusLayout(scene,retreat,rooms){
 for(const [id,objects] of members){const a=byId(id),b=campusLayout.find(b=>b[0]===id);for(const o of objects){o.position.x+=b[4]-a[4];o.position.z-=b[5]-a[5];}}
 for(const part of sharedVertices){const a=byId(part.id),b=campusLayout.find(b=>b[0]===part.id),p=part.geometry.attributes.position;for(const i of part.indices)p.setXYZ(i,p.getX(i)+(b[4]-a[4])/part.scale,p.getY(i),p.getZ(i)-(b[5]-a[5])/part.scale);p.needsUpdate=true;part.geometry.computeBoundingBox();part.geometry.computeBoundingSphere();}
 rooms.forEach((r,i)=>r.root.position.add(buildingOffset(i?'07':'01B')));

 for(const lamp of scene.children.filter(o=>o.isPointLight||o.isSpotLight)){const b=owner(lamp.position.x/S,lamp.position.z/S);lamp.position.add(buildingOffset(b[0]));if(lamp.target)lamp.target.position.add(buildingOffset(b[0]));}

 const top=.275*S,bottom=retreat.site.seaLevel-1;
 for(const b of campusLayout)if(b[0]!=='G'){
  const bounds=[anchor+b[4]-b[6]/2,anchor+b[4]+b[6]/2,-b[5]-b[7]/2,-b[5]+b[7]/2];
  const delta=buildingOffset(b[0]),hole=LECTERN_SHAFT_PLAN.map((v,i)=>v*S+(i<2?delta.x:delta.z));
  for(const [a,c,d,e] of (b[0]==='01B'?subtractRect(bounds,hole):[bounds])){
   const m=new T.Mesh(new T.BoxGeometry(c-a,top-bottom,e-d),[retreat.materials.edge,retreat.materials.edge,retreat.materials.stone,retreat.materials.edge,retreat.materials.edge,retreat.materials.edge]);m.position.set((a+c)/2,(top+bottom)/2,(d+e)/2);m.receiveShadow=m.castShadow=true;m.name='Campus platform '+b[0];scene.add(m);
  }
 }
 if(retreat.campus?.lectern)retreat.campus.lecternLift=createLecternLift(scene,retreat.campus.lectern,retreat.campus.carpetMaterial,buildingOffset('01B'));
 if(retreat.campus){const [a,b,c,d]=LECTERN_SHAFT_PLAN,delta=buildingOffset('01C'),cap=new T.Mesh(new T.BoxGeometry((b-a)*S,.024*S,(d-c)*S),retreat.campus.carpetMaterial);cap.position.set((a+b)/2*S+delta.x,(.28+.016)*S,(c+d)/2*S+delta.z);cap.receiveShadow=true;cap.name='Backup hall fixed lectern floor';scene.add(cap);}
 const bridges=new T.Group();bridges.name='September 26 campus bridges';scene.add(bridges);
 function deck(x,y,w,d,rotation=0){const m=new T.Mesh(new T.BoxGeometry(w,.28,d),retreat.materials.timber);m.position.set(anchor+x,top-.14,-y);m.rotation.y=rotation;m.receiveShadow=true;bridges.add(m);}
 const g=campusLayout.find(b=>b[0]==='G'),x=g[4],y=g[5],w=g[6],d=g[7];for(const a of [[x-w/2,y,3,d+3],[x+w/2,y,3,d+3],[x,y-d/2,w,3],[x,y+d/2,w,3],[x,y,3,d],[x,y,w,3]])deck(...a);
 for(const [a,b] of bridgePlan.connections){const path=routeBridge(campusLayout.find(r=>r[0]===a),campusLayout.find(r=>r[0]===b),campusLayout);if(!path)throw Error('无法连接 '+a+'/'+b);for(const v of path.slice(1,-1))deck(v[0],v[1],3,3);for(let i=1;i<path.length;i++){const p=path[i-1],q=path[i];deck((p[0]+q[0])/2,(p[1]+q[1])/2,3,Math.hypot(q[0]-p[0],q[1]-p[1]),Math.atan2(q[0]-p[0],-(q[1]-p[1])));}}
 createHallSpiral(scene,retreat.materials,buildingOffset('01B'));
 const pavilion=createSeaPavilion(scene,retreat.materials,buildingOffset('01B'));if(retreat.campus)retreat.campus.seaPavilion=pavilion;
 scene.updateMatrixWorld(true);
 const ray=new T.Raycaster(),down=new T.Vector3(0,-1,0);
 if(typeof document!=='undefined')for(const b of [...campusLayout,['10','住宅',0,0,retreat.residence?.root.position.x-anchor||0,-(retreat.residence?.root.position.z||0),110,86]]){
   if(b[0]==='10'&&!retreat.residence)continue;
   const x=anchor+b[4],z=-b[5];ray.set(new T.Vector3(x,60,z),down);
   const hits=ray.intersectObjects(scene.children.filter(o=>o.visible&&o.name!=='September 26 campus bridges'),true).filter(h=>h.object.isMesh&&!h.object.material?.transparent&&h.point.y<40);
   const y=hits.length?hits[0].point.y:.4;
   createRoofNumber(scene,b[0]==='01B'?'1':b[0],x,y+.05,z,Math.min(11,b[6]*.42),Math.min(11,b[7]*.42));
 }
}
export function relocateShots(shots){
 const hall=buildingOffset('01B'),west=HALL.west*S+hall.x,south=HALL.south*S+hall.z,p=[west-14,10,south+10],t=[west-3,3,south-2];shots.push({name:'旋转楼梯',title:'南侧起步，绕西侧上楼。',description:'原有木踏步、金属扶手与踏步灯 · 弧形旋转楼梯',duration:25,fov:58,positions:[p,p.slice()],targets:[t,t.slice()]});

 for(const [name,id] of [['报告厅备份','01C'],['访客小院','06'],['休息室二组','R2']]){const b=campusLayout.find(r=>r[0]===id),p=[anchor+b[4]-35,18,-b[5]+32],t=[anchor+b[4],2,-b[5]];shots.push({name,title:name,description:'新布局 · 海上栈桥连接',duration:25,fov:58,positions:[p,p.slice()],targets:[t,t.slice()]});}

 const ids={'报告厅':'01B','板书':'01B','二楼客厅':'01B','海景露台':'01B','教学楼':'07','书室':'02','学术客厅':'03','楼上书房':'03','讨论楼':'04','楼上讨论室':'04','咖啡屋':'05N','茶室':'05S','客舍一':'R1','客舍二':'R3','海上花园':'G','庭院':'03'};
 for(const shot of shots){const id=ids[shot.name];if(id){const v=buildingOffset(id);for(const key of ['positions','targets'])shot[key]=shot[key].map(p=>[p[0]+v.x,p[1],p[2]+v.z]);}if(shot.name==='远眺'){shot.positions=[[anchor-340,240,280],[anchor-340,240,280]];shot.targets=[[anchor-70,0,-30],[anchor-70,0,-30]];}}
}
