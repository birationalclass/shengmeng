import * as T from '../3d/vendor/three.module.js';
export function boatPose(time,index){const q=time*.08+index*Math.PI*2/3,r=10.05;return {x:Math.sin(q)*r,z:Math.cos(q)*r,heading:q+Math.PI/2,y:.75+Math.sin(time*1.3+index)*.025,roll:Math.sin(time*.85+index)*.045};}
export function installPoolBoats(a,p){
 a.poolBoats??=[];const timber=a.materials.wood,trim=new T.MeshStandardMaterial({color:0x8d7959,roughness:.72});
 const outline=[[0,.9],[.25,.65],[.37,.15],[.32,-.5],[.16,-.73],[-.16,-.73],[-.32,-.5],[-.37,.15],[-.25,.65]];
 for(let index=0;index<3;index++){
  const root=new T.Group();root.userData.landmark='pool-rowboat';p.add(root);const shell=new T.MeshStandardMaterial({color:[0xe4ddd0,0x9dc4d0,0xc8b396][index],roughness:.66,side:T.DoubleSide}),vertices=[];
  for(let k=0;k<outline.length;k++){const A=outline[k],B=outline[(k+1)%outline.length];vertices.push(A[0],.17,A[1],A[0]*.48,-.08,A[1]*.76,B[0]*.48,-.08,B[1]*.76,A[0],.17,A[1],B[0]*.48,-.08,B[1]*.76,B[0],.17,B[1]);}
  const hull=new T.BufferGeometry();hull.setAttribute('position',new T.Float32BufferAttribute(vertices,3));hull.computeVertexNormals();a.mesh(root,hull,shell);a.box(root,[.30,.035,1.02],[0,-.045,-.02],timber);
  for(let k=0;k<outline.length;k++){const A=outline[k],B=outline[(k+1)%outline.length];a.rod(root,[A[0],.18,A[1]],[B[0],.18,B[1]],.025,trim);}
  for(const z of [-.36,.20])a.box(root,[.57,.055,.15],[0,.11,z],timber);
  for(const side of [-1,1]){a.rod(root,[side*.17,.18,-.12],[side*.67,.06,-.60],.02,trim);const paddle=a.box(root,[.11,.025,.27],[side*.71,.055,-.65],timber);paddle.rotation.y=-side*.65;}
  const wake=new T.Group();p.add(wake);const trails=[];
  for(const side of [-1,1]){const geo=new T.BufferGeometry();geo.setAttribute('position',new T.BufferAttribute(new Float32Array(28*3),3));const line=new T.Line(geo,new T.LineBasicMaterial({color:0xd8f2f4,transparent:true,opacity:.48,depthWrite:false}));line.renderOrder=3;wake.add(line);trails.push({line,side});}
  a.poolBoats.push({root,wake,trails,index});
 }
 updatePoolBoats(a.poolBoats,0,false,false);
}
export function updatePoolBoats(boats,time,reduced=false,ready=true){for(const b of boats||[]){const t=reduced?0:time,p=boatPose(t,b.index);b.root.position.set(p.x,p.y,p.z);b.root.rotation.set(0,p.heading,reduced?0:p.roll);b.wake.visible=ready&&!reduced;
 for(const {line,side}of b.trails){const attr=line.geometry.attributes.position;for(let k=0;k<attr.count;k++){const age=.9+k/(attr.count-1)*2.4,q=boatPose(t-age,b.index),spread=.08+age*.075;attr.setXYZ(k,q.x+side*q.x/10.05*spread,.713,q.z+side*q.z/10.05*spread);}attr.needsUpdate=true;line.geometry.computeBoundingSphere();}
}}
