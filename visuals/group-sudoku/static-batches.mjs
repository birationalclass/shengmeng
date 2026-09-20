import * as T from '../3d/vendor/three.module.js';
// Collapse repeated stationary components after construction. Animated joints and
// the live board retain their own transforms and materials.
export function batchBuiltDomain(atlas,board){
 if(board.staticBatch){for(const object of board.batchedSources)object.visible=false;return;}
 const dynamic=new Set([board.lift,board.glow,...atlas.rotating.map(t=>t.object),...(atlas.detailMotion||[]).map(t=>t.object),...(atlas.clockworkLifts||[])]),groups=new Map();
 board.content.updateWorldMatrix(true,true);
 board.content.traverse(o=>{if(!o.isMesh||o.isInstancedMesh||Array.isArray(o.material))return;for(let p=o;p&&p!==board.content;p=p.parent)if(dynamic.has(p))return;const key=[o.geometry.uuid,o.material.uuid,o.castShadow,o.receiveShadow].join(':');if(!groups.has(key))groups.set(key,[]);groups.get(key).push(o);});
 const root=new T.Group(),inverse=board.content.matrixWorld.clone().invert();board.batchedSources=[];
 for(const meshes of groups.values()){if(meshes.length<3)continue;const first=meshes[0],batch=new T.InstancedMesh(first.geometry,first.material,meshes.length);batch.castShadow=first.castShadow;batch.receiveShadow=first.receiveShadow;meshes.forEach((o,i)=>{batch.setMatrixAt(i,new T.Matrix4().multiplyMatrices(inverse,o.matrixWorld));o.visible=false;board.batchedSources.push(o);});batch.computeBoundingSphere();root.add(batch);}
 board.staticBatch=root;board.content.add(root);
}
