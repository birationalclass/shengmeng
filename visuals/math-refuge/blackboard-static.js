// Batch immutable auditorium geometry without changing its vertices or materials.
function signature(g){return Object.entries(g.attributes).map(([n,a])=>n+':'+a.itemSize+':'+a.normalized).sort().join('|');}
export function mergeGeometry(T,geometries){
 const out=new T.BufferGeometry(),names=Object.keys(geometries[0].attributes),indices=[];let offset=0;
 for(const g of geometries){const index=g.index;for(let i=0;i<(index?.count??g.attributes.position.count);i++)indices.push(offset+(index?index.getX(i):i));offset+=g.attributes.position.count;}
 for(const name of names){const first=geometries[0].attributes[name],ArrayType=first.array.constructor,total=geometries.reduce((n,g)=>n+g.attributes[name].array.length,0),array=new ArrayType(total);let at=0;for(const g of geometries){array.set(g.attributes[name].array,at);at+=g.attributes[name].array.length;}out.setAttribute(name,new T.BufferAttribute(array,first.itemSize,first.normalized));}
 out.setIndex(indices);out.computeBoundingBox();out.computeBoundingSphere();return out;
}
export function batchStaticHall(T,root,{exclude=[],freeze=true,opaqueOnly=false,bucket=()=>''}={}){
 root.updateWorldMatrix(true,true);const inverseRoot=root.matrixWorld.clone().invert(),groups=new Map(),original=[],relative=new Map();root.traverse(o=>{if(!o.isMesh)return;if(opaqueOnly&&(o.material?.transparent||o.material?.colorWrite===false||'action' in o.userData))return;for(let p=o;p&&p!==root;p=p.parent)if(exclude.includes(p))return;original.push(o);relative.set(o,new T.Matrix4().multiplyMatrices(inverseRoot,o.matrixWorld));});const before=original.length;
 for(const mesh of original){if(Array.isArray(mesh.material))continue;mesh.updateMatrix();const key=mesh.material.uuid+':'+Boolean(mesh.isInstancedMesh)+':'+(mesh.count||0)+':'+signature(mesh.geometry)+':'+(mesh.userData.action||'')+':'+bucket(mesh,relative.get(mesh));if(!groups.has(key))groups.set(key,[]);groups.get(key).push(mesh);}
 let batches=0;
 for(const meshes of groups.values()){
  if(meshes.length<2)continue;
  const first=meshes[0],instanced=first.isInstancedMesh,firstMatrix=new T.Matrix4(),local=new T.Matrix4(),geometries=[];
  for(const mesh of meshes){const g=mesh.geometry.clone();if(instanced){mesh.getMatrixAt(0,local);local.premultiply(relative.get(mesh));}else local.copy(relative.get(mesh));g.applyMatrix4(local);geometries.push(g);}
  const geometry=mergeGeometry(T,geometries);geometries.forEach(g=>g.dispose());let combined;
  if(instanced){combined=new T.InstancedMesh(geometry,first.material,first.count);first.getMatrixAt(0,firstMatrix);firstMatrix.premultiply(relative.get(first)).invert();for(let i=0;i<first.count;i++){first.getMatrixAt(i,local);local.premultiply(relative.get(first)).multiply(firstMatrix);combined.setMatrixAt(i,local);}combined.computeBoundingSphere();}
  else combined=new T.Mesh(geometry,first.material);
  combined.userData={...first.userData};combined.name='Batched auditorium '+first.material.uuid;combined.castShadow=first.castShadow;combined.receiveShadow=first.receiveShadow;
  meshes.forEach(m=>m.removeFromParent());root.add(combined);batches++;
 }
 root.updateMatrixWorld(true);if(freeze)root.traverse(o=>{o.updateMatrix();o.matrixAutoUpdate=false;o.matrixWorldAutoUpdate=false;});
 return{before,after:before-[...groups.values()].filter(g=>g.length>1).reduce((n,g)=>n+g.length-1,0),batches};
}
