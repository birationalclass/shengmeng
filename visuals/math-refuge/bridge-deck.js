import * as T from '../3d/vendor/three.module.js';
// Cut every slab to the curve, with common cross-sections instead of rotated boxes.
export function curvedDeck(curve,width,count,material,columns=1,thickness=.08){
 const vertices=[],uv=[],length=curve.getLength(),gap=.016;
 const point=(u,lateral,drop=0)=>{const p=curve.getPointAt(u),d=curve.getTangentAt(u);return p.add(new T.Vector3(-d.z,0,d.x).multiplyScalar(lateral)).add(new T.Vector3(0,-drop,0));};
 const quad=(a,b,c,d)=>{for(const p of [a,c,b,a,d,c]){vertices.push(...p.toArray());uv.push(p.x*.0565685,p.z*.0565685);}};
 for(let i=0;i<count;i++){
  const a=i/count+(i?gap/length/2:0),b=(i+1)/count-(i<count-1?gap/length/2:0);
  for(let j=0;j<columns;j++){
   const section=u=>{const w=width(u),lo=-w/2+w*j/columns+(j?gap/2:0),hi=-w/2+w*(j+1)/columns-(j<columns-1?gap/2:0);return [point(u,lo),point(u,hi),point(u,lo,thickness),point(u,hi,thickness)];};
   const [al,ar,abl,abr]=section(a),[bl,br,bbl,bbr]=section(b);
   quad(al,bl,br,ar);quad(abl,abr,bbr,bbl);quad(al,ar,abr,abl);quad(bl,bbl,bbr,br);quad(al,abl,bbl,bl);quad(ar,br,bbr,abr);
  }
 }
 const geometry=new T.BufferGeometry();geometry.setAttribute('position',new T.Float32BufferAttribute(vertices,3));geometry.setAttribute('uv',new T.Float32BufferAttribute(uv,2));geometry.computeVertexNormals();
 const mesh=new T.Mesh(geometry,material);mesh.castShadow=mesh.receiveShadow=true;mesh.name='Curve-cut stone deck';return mesh;
}
