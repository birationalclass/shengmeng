import * as T from '../vendor/three.module.js';

// Smooth shape-preserving Hermite interpolation of independent section controls.
export function profile(values,u){
 const n=values.length-1,x=T.MathUtils.clamp(u,0,1)*n,i=Math.min(n-1,Math.floor(x)),t=x-i;
 const d=values.slice(1).map((v,k)=>v-values[k]);
 const slope=k=>k===0?d[0]:k===n?d[n-1]:d[k-1]*d[k]<=0?0:2*d[k-1]*d[k]/(d[k-1]+d[k]);
 return (2*t*t*t-3*t*t+1)*values[i]+(t*t*t-2*t*t+t)*slope(i)+(-2*t*t*t+3*t*t)*values[i+1]+(t*t*t-t*t)*slope(i+1);
}

export function prepareStroke(spec){
 const curve=new T.CatmullRomCurve3(spec.points.map(p=>new T.Vector3(...p)),false,'centripetal');curve.arcLengthDivisions=1800;
 const count=600,centers=[],tangents=[],normals=[],binormals=[];
 for(let i=0;i<=count;i++){centers.push(curve.getPointAt(i/count));tangents.push(curve.getTangentAt(Math.min(.999999,Math.max(.000001,i/count))).normalize())}
 const seed=new T.Vector3(0,0,1);if(Math.abs(seed.dot(tangents[0]))>.95)seed.set(0,1,0);
 normals[0]=new T.Vector3().crossVectors(seed,tangents[0]).normalize();
 binormals[0]=new T.Vector3().crossVectors(tangents[0],normals[0]).normalize();
 // Double reflection transport, Wang et al., ACM TOG 27(1), 2008.
 for(let i=1;i<=count;i++){
  const v1=centers[i].clone().sub(centers[i-1]),c1=v1.lengthSq();
  const rL=normals[i-1].clone().addScaledVector(v1,-2*v1.dot(normals[i-1])/c1);
  const tL=tangents[i-1].clone().addScaledVector(v1,-2*v1.dot(tangents[i-1])/c1);
  const v2=tangents[i].clone().sub(tL),c2=v2.lengthSq();
  const r=c2>1e-14?rL.addScaledVector(v2,-2*v2.dot(rL)/c2):rL;
  normals[i]=r.addScaledVector(tangents[i],-r.dot(tangents[i])).normalize();
  binormals[i]=new T.Vector3().crossVectors(tangents[i],normals[i]).normalize();
 }
 return {...spec,curve,count,centers,tangents,normals,binormals};
}

export function sampleSection(s,u,{flat=false,fullness=1}={}){
 const center=s.curve.getPointAt(u),tan=s.curve.getTangentAt(Math.min(.999999,Math.max(.000001,u))).normalize();
 const f=u*s.count,i=Math.min(s.count-1,Math.floor(f));
 let n=s.normals[i].clone().lerp(s.normals[i+1],f-i);n.addScaledVector(tan,-n.dot(tan)).normalize();
 let b=new T.Vector3().crossVectors(tan,n).normalize(),angle=profile(s.roll,u);
 const rn=n.clone().multiplyScalar(Math.cos(angle)).addScaledVector(b,Math.sin(angle)),rb=n.clone().multiplyScalar(-Math.sin(angle)).addScaledVector(b,Math.cos(angle));n=rn;b=rb;
 const head=Math.min(1,u/(s.entry||.055)),tail=Math.min(1,(1-u)/(s.exit||.08));
 const cap=Math.sqrt(Math.max(0,head*(2-head)))*Math.sqrt(Math.max(0,tail*(2-tail)));
 let width=profile(s.width,u)*cap,thickness=profile(s.thickness,u)*cap*fullness;
 if(flat){center.z=0;thickness=width*.19;n.set(-tan.y,tan.x,0).normalize();b.set(0,0,1)}
 return {center,tan,n,b,width,thickness};
}

export function createStrokeGeometry(L=240,R=48){
 // Shared circumference vertices and single poles: no normal seam or duplicate caps.
 const count=2+(L-1)*R,positions=new Float32Array(count*3),indices=[];
 const at=(j,k)=>1+(j-1)*R+(k+R)%R,end=count-1;
 for(let k=0;k<R;k++)indices.push(0,at(1,k+1),at(1,k));
 for(let j=1;j<L-1;j++)for(let k=0;k<R;k++){const a=at(j,k),c=at(j,k+1),b=at(j+1,k),d=at(j+1,k+1);indices.push(a,c,b,b,c,d)}
 for(let k=0;k<R;k++)indices.push(at(L-1,k),at(L-1,k+1),end);
 const geometry=new T.BufferGeometry();geometry.setAttribute('position',new T.BufferAttribute(positions,3).setUsage(T.DynamicDrawUsage));geometry.setIndex(indices);geometry.userData={L,R};return geometry;
}

export function updateStrokeGeometry(geometry,s,progress=1,options={}){
 const {L,R}=geometry.userData,positions=geometry.attributes.position.array,p=Math.max(.00001,progress);
 const start=sampleSection(s,0,options).center,finish=sampleSection(s,p,options).center;start.toArray(positions,0);finish.toArray(positions,positions.length-3);
 for(let j=1;j<L;j++){
  const u=p*j/L,sec=sampleSection(s,u,options);
  const head=p<.99999?Math.sqrt(Math.max(0,1-Math.pow(1-Math.min(1,(p-u)/Math.min(.04,p*.3)),2))):1;
  for(let k=0;k<R;k++){
   const a=k/R*Math.PI*2,q=sec.center.clone().addScaledVector(sec.n,sec.width*Math.cos(a)*head).addScaledVector(sec.b,sec.thickness*Math.sin(a)*head);
   q.toArray(positions,(1+(j-1)*R+k)*3);
  }
 }
 geometry.attributes.position.needsUpdate=true;geometry.computeVertexNormals();geometry.computeBoundingBox();geometry.computeBoundingSphere();return geometry;
}
