import * as T from '../3d/vendor/three.module.js';
// Smooth the existing safe connection rather than moving any building anchors.
export function bridgeCurve(path,buildings,ends,width=3){
 const blocked=points=>points.some(([x,y])=>buildings.some(b=>!ends.includes(b[0])&&Math.abs(x-b[4])<b[6]/2+width/2+.1&&Math.abs(y-b[5])<b[7]/2+width/2+.1));
 if(path.length===2){
  const [a,b]=path,dx=b[0]-a[0],dy=b[1]-a[1],length=Math.hypot(dx,dy);
  for(const bow of [Math.min(6,length*.07),-Math.min(6,length*.07),1,-1,0]){
   const points=Array.from({length:81},(_,i)=>{const t=i/80,s=bow*Math.sin(Math.PI*t)**2;return [a[0]+dx*t-dy/length*s,a[1]+dy*t+dx/length*s];});
   if(!blocked(points))return points;
  }
 }
 const curve=new T.CatmullRomCurve3(path.map(p=>new T.Vector3(p[0],0,p[1])),false,'centripetal');
 const smooth=curve.getPoints(200).map(p=>[p.x,p.z]);
 if(!blocked(smooth))return smooth;
 // Small rounded corners stay inside the original visibility route's clearance.
 const result=[path[0]];
 for(let i=1;i<path.length-1;i++){
  const a=path[i-1],p=path[i],b=path[i+1],la=Math.hypot(p[0]-a[0],p[1]-a[1]),lb=Math.hypot(b[0]-p[0],b[1]-p[1]),r=Math.min(.22,la/3,lb/3);
  const u=p.map((v,k)=>v+(a[k]-v)*r/la),v=p.map((q,k)=>q+(b[k]-q)*r/lb);
  result.push(u);for(let j=1;j<=10;j++){const t=j/10;result.push(p.map((q,k)=>(1-t)**2*u[k]+2*(1-t)*t*q+t*t*v[k]));}
 }
 result.push(path.at(-1));return result;
}
export function createCoastalBridge(parent,points,materials,anchor,top,name){
 const group=new T.Group();group.name=name;parent.add(group);
 const curve=new T.CatmullRomCurve3(points.map(([x,y])=>new T.Vector3(anchor+x,top,-y)),false,'centripetal');
 const length=curve.getLength(),batches=new Map(),matrix=new T.Matrix4(),quat=new T.Quaternion();
 const deck=materials.hallPaving||materials.terraceFloor||materials.stone;
 function part(p,size,mat,yaw=0){if(!batches.has(mat))batches.set(mat,[]);matrix.compose(p,quat.setFromAxisAngle(new T.Vector3(0,1,0),yaw),new T.Vector3(...size));batches.get(mat).push(matrix.clone());}
 const n=Math.ceil(length/1.15);
 for(let i=0;i<n;i++){
  const u=(i+.5)/n,p=curve.getPointAt(u),d=curve.getTangentAt(u),yaw=Math.atan2(d.x,d.z),side=new T.Vector3(-d.z,0,d.x);
  for(const s of [-1,1])part(p.clone().addScaledVector(side,s*.75).add(new T.Vector3(0,-.08,0)),[1.495,.16,length/n-.006],deck,yaw);
  for(const s of [-1,1])part(p.clone().addScaledVector(side,s*1.47).add(new T.Vector3(0,-.17,0)),[.065,.22,length/n+.015],materials.edge,yaw);
 }
 const supports=Math.ceil(length/5.5);
 for(let i=0;i<=supports;i++){
  const u=i/supports,p=curve.getPointAt(u),d=curve.getTangentAt(u),side=new T.Vector3(-d.z,0,d.x),yaw=Math.atan2(d.x,d.z);
  part(p.clone().add(new T.Vector3(0,-.31,0)),[2.9,.18,.18],materials.steel,yaw);
  for(const s of [-1,1])part(p.clone().addScaledVector(side,s*1.12).add(new T.Vector3(0,-3.2,0)),[.22,6,.22],materials.steel);
 }
 for(const [mat,items] of batches){const mesh=new T.InstancedMesh(new T.BoxGeometry(),mat,items.length);items.forEach((m,i)=>mesh.setMatrixAt(i,m));mesh.castShadow=mesh.receiveShadow=true;mesh.computeBoundingSphere();group.add(mesh);}
 group.userData={length,width:3,curved:true,stoneDeck:true};return group;
}
