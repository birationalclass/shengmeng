import * as T from 'three';
import {BUILDING_SCALE as S} from './site-layout.js';
import {createDesignTools} from './design-tools.js';
import {installLayoutEditor} from './layout-editor.js';
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
    for(const dest of destinations(b)){const unit=worldInstances?1:S;const transform=new T.Matrix4().makeScale(1/unit,1/unit,1/unit).multiply(relocation(dest)).multiply(new T.Matrix4().makeScale(unit,unit,unit));const matrix=scratch.clone().premultiply(transform);if(!chunks.has(dest[0]))chunks.set(dest[0],[]);matrix.designGroup=obj.userData.designGroups?.[i]||'';chunks.get(dest[0]).push(matrix);}
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
export function setupLayoutPreview({scene,retreat,camera,controls,rooms,stop,setHour,onMove}){
 // Move board assemblies built after createRetreat, preserving the original scripts.
 rooms.forEach((r,i)=>{r.root.position.add(offset(byId(i?'07':'01B')));r.root.updateMatrixWorld(true);track(r.root,i?'07':'01B');});
 retreat.updateGeometryLOD=()=>{};
 for(const lamp of scene.children.filter(o=>o.isPointLight||o.isSpotLight)){
  const b=owner(lamp.position.x/S,lamp.position.z/S);lamp.position.add(offset(b));track(lamp,b[0]);if(lamp.target){lamp.target.position.add(offset(b));track(lamp.target,b[0]);}
 }
 const platformMaterial=retreat.materials.stone,edge=retreat.materials.edge,top=.275*S;
 function slab(b){const bottom=retreat.site.seaLevel-1;const m=new T.Mesh(new T.BoxGeometry(b[6],top-bottom,b[7]),[edge,edge,platformMaterial,edge,edge,edge]);m.position.set(anchor+b[4],(top+bottom)/2,-b[5]);m.castShadow=m.receiveShadow=true;scene.add(track(m,b[0]));}
 for(const b of layout)if(b[0]!=='G')slab(b);
 const home=retreat.residence.root;layout.push(['10','独立住宅',0,0,home.position.x-anchor,-home.position.z,110,86]);track(home,'10');
 // Garden trays are original geometry; the connecting deck is deliberately narrow.
 const bridgeGroup=new T.Group();scene.add(bridgeGroup);
 const guide=new T.Group();guide.name='10m grid and 90 degree sunset corridor';scene.add(guide);
 const pts=[];for(let x=-290;x<=110;x+=10)pts.push(anchor+x,top+.07,-400,anchor+x,top+.07,270);for(let y=-270;y<=400;y+=10)pts.push(anchor-290,top+.07,-y,anchor+110,top+.07,-y);
 guide.add(new T.LineSegments(new T.BufferGeometry().setAttribute('position',new T.Float32BufferAttribute(pts,3)),new T.LineBasicMaterial({color:0xd8d9cc,transparent:true,opacity:.23,depthWrite:false})));
 const wx=anchor-62-4.2*S,hy=11.5*S,far=anchor-285,fy=hy+wx-far;
 for(const sign of [-1,1])guide.add(track(new T.Line(new T.BufferGeometry().setFromPoints([new T.Vector3(wx,top+.1,sign*hy),new T.Vector3(far,top+.1,sign*fy)]),new T.LineBasicMaterial({color:0xf2b967})),'01B'));
 const labels=new T.Group();scene.add(labels);
 for(const b of layout){const c=document.createElement('canvas');c.width=512;c.height=100;const ctx=c.getContext('2d');ctx.fillStyle='#102625dd';ctx.fillRect(0,0,512,100);ctx.fillStyle='#fff0cd';ctx.font='32px sans-serif';ctx.textAlign='center';ctx.fillText(b[0]+' '+b[1],256,63);const tex=new T.CanvasTexture(c);tex.colorSpace=T.SRGBColorSpace;const sprite=new T.Sprite(new T.SpriteMaterial({map:tex,depthTest:false,depthWrite:false}));sprite.position.set(anchor+b[4],b[0]==='07'?20:14,-b[5]);sprite.scale.set(32,6.25,1);labels.add(track(sprite,b[0]));}
 const bar=document.createElement('aside');bar.id='layoutPreviewBar';bar.innerHTML='<strong>难民营设计 · 10 米网格</strong><span>建筑 · 装饰 · 平台连桥</span><div><button data-view="all">总览</button><button data-view="01B">01B 报告厅</button><button data-view="west">报告厅看日落</button><button data-view="01C">01C 固定备份</button><button data-view="north">北侧群落</button><button data-view="south">南侧群落</button></div><label><input id="layoutGrid" type="checkbox" checked>10m 网格 / 观景边界</label><label><input id="layoutLabels" type="checkbox" checked>建筑编号</label><a href="../math-refuge/?qa=arrival137" target="_blank" rel="noopener">打开原版对照</a><small>左键观察 · 右键移动建筑 · 滚轮前后 · W/S 前后，A/D 转向，Q/E 平移，空格/X 升降</small>';
 document.body.append(bar);
 document.getElementById('layoutGrid').onchange=e=>guide.visible=e.target.checked;
 document.getElementById('layoutLabels').onchange=e=>labels.visible=e.target.checked;
 function focus(view){stop();let p,t;
  if(view==='all'){p=[anchor-390,370,490];t=[anchor-115,0,-70];}
  else if(view==='west'){const hall=byId('01B');p=[anchor+hall[4],2.1,-hall[5]];t=[anchor+hall[4]-400,2.1,-hall[5]];setHour('sunset');}
  else if(view==='north'){p=[anchor-370,185,-80];t=[anchor-160,0,-245];}
  else if(view==='south'){p=[anchor-340,145,40];t=[anchor-160,0,175];}
  else{const b=byId(view);p=[anchor+b[4]-50,22,-b[5]+52];t=[anchor+b[4],3,-b[5]];}
  camera.position.fromArray(p);controls.target.fromArray(t);camera.fov=55;camera.updateProjectionMatrix();controls.update();
 }
 bar.querySelectorAll('[data-view]').forEach(b=>b.onclick=()=>focus(b.dataset.view));
 const design=createDesignTools({bar,layout,members,scene,camera,controls,anchor,materials:retreat.materials,bridgeGroup});
 installLayoutEditor({bar,layout,members,sharedVertices,scene,anchor,focus,stop,design,onMove:()=>{design.update();onMove?.();}});
 focus('all');return {focus};
}
