import * as T from '../3d/vendor/three.module.js';
// Cut every slab to the curve, with common cross-sections instead of rotated boxes.
export function curvedDeck(curve,width,count,material,columns=1,thickness=.08){
 const vertices=[],uv=[],groups=[],length=curve.getLength(),gap=.03;
 const point=(u,lateral,drop=0)=>{const p=curve.getPointAt(u),d=curve.getTangentAt(u);return p.add(new T.Vector3(-d.z,0,d.x).multiplyScalar(lateral)).add(new T.Vector3(0,-drop,0));};
 const quad=(a,b,c,d,mat=0)=>{groups.push({start:vertices.length/3,count:6,materialIndex:mat});for(const p of [a,c,b,a,d,c]){vertices.push(...p.toArray());uv.push(p.x*.0565685,p.z*.0565685);}};
 for(let i=0;i<count;i++){
  const a=i/count+(i?gap/length/2:0),b=(i+1)/count-(i<count-1?gap/length/2:0);
  for(let j=0;j<columns;j++){
   const section=u=>{const w=width(u),lo=-w/2+w*j/columns+(j?gap/2:0),hi=-w/2+w*(j+1)/columns-(j<columns-1?gap/2:0);return [point(u,lo),point(u,hi),point(u,lo,thickness),point(u,hi,thickness)];};
   const [al,ar,abl,abr]=section(a),[bl,br,bbl,bbr]=section(b);
   const inset=.014;
   const along=Math.min(.18,inset/al.distanceTo(bl)),across=Math.min(.18,inset/al.distanceTo(ar));
   const inner=(t,u)=>al.clone().lerp(bl,t).lerp(ar.clone().lerp(br,t),u);
   const il=inner(along,across),ir=inner(along,1-across),jl=inner(1-along,across),jr=inner(1-along,1-across);
   quad(il,jl,jr,ir);quad(al,bl,jl,il,1);quad(bl,br,jr,jl,1);quad(br,ar,ir,jr,1);quad(ar,al,il,ir,1);
   quad(abl,abr,bbr,bbl);quad(al,ar,abr,abl);quad(bl,bbl,bbr,br);quad(al,abl,bbl,bl);quad(ar,br,bbr,abr);
  }
 }
 const geometry=new T.BufferGeometry(),ordered=[],orderedUv=[];
 for(const mat of [0,1]){
  const start=ordered.length/3;
  for(const g of groups)if(g.materialIndex===mat){ordered.push(...vertices.slice(g.start*3,(g.start+g.count)*3));orderedUv.push(...uv.slice(g.start*2,(g.start+g.count)*2));}
  geometry.addGroup(start,ordered.length/3-start,mat);
 }
 geometry.setAttribute('position',new T.Float32BufferAttribute(ordered,3));geometry.setAttribute('uv',new T.Float32BufferAttribute(orderedUv,2));geometry.computeVertexNormals();
 const border=material.clone();border.color.multiplyScalar(.62);border.roughness=.82;border.metalness=.12;
 const mesh=new T.Mesh(geometry,[material,border]);mesh.castShadow=mesh.receiveShadow=true;mesh.name='Curve-cut stone deck';return mesh;
}
