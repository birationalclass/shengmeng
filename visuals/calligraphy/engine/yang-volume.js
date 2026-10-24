import * as T from '../vendor/three.module.js';
import {profile,createStrokeGeometry} from './stroke-volume.js';
import {pairBoundaryCurves} from './contour-correspondence.js';

// Interpretive implementation of Lin, Zheng et al., Floating Strokes (2025),
// sec. 4.1: two independently authored boundary curves and two orthogonal
// volume curves. These controls are ours; no original artist model is included.
// Open, clamped cubic B-splines give C2 continuity between simple inner knots.
function spline(points){
 const p=Math.min(3,points.length-1),n=points.length,knots=[];
 for(let i=0;i<n+p+1;i++)knots.push(i<=p?0:i>=n?1:(i-p)/(n-p));
 const controls=points.map(a=>new T.Vector3(...a));
 return u=>{
  u=T.MathUtils.clamp(u,0,1);let k=p;
  if(u===1)k=n-1;else while(k<n-1&&knots[k+1]<=u)k++;
  const d=Array.from({length:p+1},(_,j)=>controls[k-p+j].clone());
  for(let r=1;r<=p;r++)for(let j=p;j>=r;j--){
   const index=k-p+j,den=knots[index+p-r+1]-knots[index];
   d[j].lerpVectors(d[j-1],d[j],den?(u-knots[index])/den:0);
  }
  return d[p];
 };
}

// C2 natural cubic interpolation for points traced ON an image contour.
// Those samples are not B-spline control vertices: approximating them would
// shrink the shoulders and erase the upward return. Both sides use the same
// scaffold knots, so the authored correspondence is retained.
function contourSpline(points,knots){
 const p=points.map(v=>new T.Vector3(...v)),n=p.length,lower=[],diagonal=[],upper=[],rhs=[];
 for(let i=1;i<n-1;i++){
  const a=knots[i]-knots[i-1],b=knots[i+1]-knots[i];
  lower.push(a/6);diagonal.push((a+b)/3);upper.push(b/6);
  rhs.push(p[i+1].clone().sub(p[i]).divideScalar(b).sub(p[i].clone().sub(p[i-1]).divideScalar(a)));
 }
 for(let i=1;i<diagonal.length;i++){const ratio=lower[i]/diagonal[i-1];diagonal[i]-=ratio*upper[i-1];rhs[i].addScaledVector(rhs[i-1],-ratio);}
 const second=Array.from({length:n},()=>new T.Vector3());
 for(let i=rhs.length-1;i>=0;i--)second[i+1].copy(rhs[i]).addScaledVector(second[i+2],-upper[i]).divideScalar(diagonal[i]);
 return u=>{
  u=T.MathUtils.clamp(u,0,1);let i=0;while(i<n-2&&knots[i+1]<u)i++;
  const h=knots[i+1]-knots[i],t=(u-knots[i])/h,v=1-t;
  return p[i].clone().multiplyScalar(v).addScaledVector(p[i+1],t)
   .addScaledVector(second[i],(v*v*v-v)*h*h/6).addScaledVector(second[i+1],(t*t*t-t)*h*h/6);
 };
}

// Preserve the sign of terminal section components. Natural interpolation of
// two converging boundaries can overshoot their difference through zero and
// reopen it, producing a small unwanted horn before the actual closing tip.
function monotoneSection(points,knots){
 const fields=[0,1,2].map(axis=>{
  const y=points.map(p=>p[axis]),h=knots.slice(1).map((v,i)=>v-knots[i]),d=h.map((v,i)=>(y[i+1]-y[i])/v),m=y.map((v,i)=>{
   if(i===0)return d[0];if(i===y.length-1)return d.at(-1);if(d[i-1]*d[i]<=0)return 0;
   const w1=2*h[i]+h[i-1],w2=h[i]+2*h[i-1];return (w1+w2)/(w1/d[i-1]+w2/d[i]);
  });
  return u=>{let i=0;while(i<y.length-2&&knots[i+1]<u)i++;const t=(u-knots[i])/h[i],t2=t*t,t3=t2*t;return (2*t3-3*t2+1)*y[i]+(t3-2*t2+t)*h[i]*m[i]+(-2*t3+3*t2)*y[i+1]+(t3-t2)*h[i]*m[i+1];};
 });
 return u=>new T.Vector3(...fields.map(f=>f(T.MathUtils.clamp(u,0,1))));
}

export function prepareRailStroke(spec){
 let a,b,correspondence;
 if(spec.interpolateBoundaries){
  const centers=spec.a.map((p,i)=>new T.Vector3(...p).add(new T.Vector3(...spec.b[i])).multiplyScalar(.5)),knots=[0];
  for(let i=1;i<centers.length;i++)knots.push(knots.at(-1)+Math.max(.025,centers[i].distanceTo(centers[i-1])));
  const end=knots.at(-1);knots.forEach((v,i)=>knots[i]=v/end);
  a=contourSpline(spec.a,knots);b=contourSpline(spec.b,knots);
  if(Number.isInteger(spec.terminalSectionFrom)){
   const rawA=a,rawB=b,from=spec.terminalSectionFrom,
    difference=monotoneSection(spec.a.map((p,i)=>spec.b[i].map((v,k)=>v-p[k])),knots);
   const edges=u=>{const aa=rawA(u),bb=rawB(u),center=aa.clone().add(bb).multiplyScalar(.5),blend=T.MathUtils.smootherstep(u,knots[from],knots[Math.min(from+1,knots.length-1)]),d=bb.sub(aa).lerp(difference(u),blend);return [center.clone().addScaledVector(d,-.5),center.clone().addScaledVector(d,.5)];};
   a=u=>edges(u)[0];b=u=>edges(u)[1];
  }
 }else{a=spline(spec.a);b=spline(spec.b);}
 if(spec.matchBoundaries){const paired=pairBoundaryCurves(a,b);a=paired.a;b=paired.b;correspondence=paired.report;}
 const count=800,sections=[];
 let previousNormal=new T.Vector3(0,0,1),length=0;
 for(let i=0;i<=count;i++){
  const u=i/count,aa=a(u),bb=b(u),center=aa.clone().add(bb).multiplyScalar(.5);
  const delta=bb.clone().sub(aa),width=delta.length();
  const lo=Math.max(0,u-.0001),hi=Math.min(1,u+.0001);
  const tangent=a(hi).add(b(hi)).sub(a(lo).add(b(lo))).normalize();
  let normal=new T.Vector3().crossVectors(tangent,delta).normalize();
  if(width<1e-8||normal.lengthSq()<.1)normal=previousNormal.clone();
  // Its orientation follows the ordered rails, including intentional banking.
  // Flipping it toward a global front would reverse the surface winding of
  // strokes whose contour order runs clockwise in the image plane.
  previousNormal.copy(normal);
  if(i>0)length+=center.distanceTo(sections[i-1].center);
  sections.push({a:aa,b:bb,center,normal,tangent,length});
 }
 return {...spec,aCurve:a,bCurve:b,count,sections,length,correspondence};
}

function interpolateSection(s,u){
 // Arc-length parameterization applies to the paired rail scaffold, so already
 // written portions keep their shape when the active front advances.
 const target=u*s.length;let lo=0,hi=s.count;
 while(hi-lo>1){const m=(lo+hi)>>1;if(s.sections[m].length<target)lo=m;else hi=m}
 const x=s.sections[lo],y=s.sections[hi],v=(target-x.length)/Math.max(1e-12,y.length-x.length);
 let a=x.a.clone().lerp(y.a,v),b=x.b.clone().lerp(y.b,v);const center=a.clone().add(b).multiplyScalar(.5);
 const tangent=x.tangent.clone().lerp(y.tangent,v).normalize(),d=b.clone().sub(a);
 // Correct oblique pairings before lofting. The long axis of every section is
 // perpendicular to the local scaffold tangent, preventing sheared folds.
 // Traced surface boundaries are not a perpendicular centreline sweep.
 // Projecting their section vectors would move the actual silhouette,
 // particularly at the broad concave foot of 風.
 if(!s.boundaryLoft)d.addScaledVector(tangent,-d.dot(tangent));
 // Short elliptical caps retain a broad pressed entry or a rounded return.
 // The earlier study made every contour pair meet in a long pointed tip.
 const startCap=s.capStart||0,endCap=s.capEnd||0;
 const capFactor=(t,length)=>length>0&&t<length?Math.sqrt(Math.max(0,1-Math.pow(1-t/length,2))):1;
 d.multiplyScalar(capFactor(u,startCap)*capFactor(1-u,endCap));
 a=center.clone().addScaledVector(d,-.5);b=center.clone().addScaledVector(d,.5);
 const width=d.length(),n=new T.Vector3().crossVectors(tangent,d).normalize();
 if(n.lengthSq()<.1)n.copy(x.normal).lerp(y.normal,v).normalize();
 if(s.joinStartNormal)n.lerp(new T.Vector3(...s.joinStartNormal),1-T.MathUtils.smootherstep(u,0,.055)).normalize();
 const front=width*profile(s.front,u),back=width*profile(s.back,u),crown=profile(s.crown||[.5,.5],u),rear=profile(s.rearCrown||[.5,.5],u);
 const camber=width*profile(s.camber||[0,0],u);
 const f=a.clone().lerp(b,crown).addScaledVector(n,front),k=a.clone().lerp(b,rear).addScaledVector(n,-back);
 const interior=center.clone().addScaledVector(n,camber+(front-back)*.5);
 return {a,b,center,interior,n,d:width?d.divideScalar(width):new T.Vector3(1,0,0),width,front,back,f,k,crown,rear,camber};
}

function cubic(a,b,c,d,t){const q=1-t;return a.clone().multiplyScalar(q*q*q).addScaledVector(b,3*q*q*t).addScaledVector(c,3*q*t*t).addScaledVector(d,t*t*t)}

export function sampleRailSection(s,u){
 if(s.runSegments){
  const v=T.MathUtils.clamp(u,0,1),segment=s.runSegments.find(part=>v<part.to)||s.runSegments.at(-1),q=sampleRailSection(segment.spec,T.MathUtils.clamp((v-segment.from)/(segment.to-segment.from),0,1)),patch=s.runTransitions?.find(part=>v>=part.from&&v<=part.to);if(!patch)return q;
  const t=(v-patch.from)/(patch.to-patch.from),a=patch.a.getPoint(t),b=patch.b.getPoint(t),center=a.clone().add(b).multiplyScalar(.5),d=b.clone().sub(a),width=d.length(),tangent=patch.a.getTangent(t).add(patch.b.getTangent(t)).normalize(),n=new T.Vector3().crossVectors(tangent,d).normalize(),scale=width/Math.max(q.width,1e-9),front=q.front*scale,back=q.back*scale,camber=q.camber*scale;
  const frameBlend=T.MathUtils.smootherstep(t,0,.20)*(1-T.MathUtils.smootherstep(t,.80,1));n.lerp(q.n,1-frameBlend).normalize();
  return {...q,a,b,center,d:d.divideScalar(Math.max(width,1e-9)),n,width,front,back,camber,f:a.clone().lerp(b,q.crown).addScaledVector(n,front),k:a.clone().lerp(b,q.rear).addScaledVector(n,-back),interior:center.clone().addScaledVector(n,camber+(front-back)*.5)};
 }
 return interpolateSection(s,u);
}
export {createStrokeGeometry};

export function updateRailGeometry(g,s,progress=1){
 const {L,R}=g.userData,pos=g.attributes.position.array,p=T.MathUtils.clamp(progress,.00001,1);
 interpolateSection(s,0).center.toArray(pos,0);interpolateSection(s,p).center.toArray(pos,pos.length-3);
 for(let j=1;j<L;j++){
  const u=p*j/L,q=interpolateSection(s,u),h=.5522847498307936;
  const bToF=q.b.clone().addScaledVector(q.n,q.front*h),fToB=q.f.clone().addScaledVector(q.d,q.width*(1-q.crown)*h);
  const fToA=q.f.clone().addScaledVector(q.d,-q.width*q.crown*h),aToF=q.a.clone().addScaledVector(q.n,q.front*h);
  const aToK=q.a.clone().addScaledVector(q.n,-q.back*h),kToA=q.k.clone().addScaledVector(q.d,-q.width*q.rear*h);
  const kToB=q.k.clone().addScaledVector(q.d,q.width*(1-q.rear)*h),bToK=q.b.clone().addScaledVector(q.n,-q.back*h);
  const quadrants=[[q.b,bToF,fToB,q.f],[q.f,fToA,aToF,q.a],[q.a,aToK,kToA,q.k],[q.k,kToB,bToK,q.b]];
  const head=p<.99999?Math.sqrt(Math.max(0,1-Math.pow(1-Math.min(1,(p-u)/Math.min(.028,p*.25)),2))):1;
  for(let k=0;k<R;k++){
   const v=k/R*4,index=Math.floor(v),point=cubic(...quadrants[index],v-index);
   // Bend the whole section into a shallow scoop without removing its solid
   // back. The shift and its derivative vanish at both contour edges.
   const theta=k/R*Math.PI*2;
   point.addScaledVector(q.n,q.camber*Math.sin(theta)**2);
   point.sub(q.center).multiplyScalar(head).add(q.center).toArray(pos,(1+(j-1)*R+k)*3);
  }
 }
 g.attributes.position.needsUpdate=true;g.computeVertexNormals();g.computeBoundingBox();g.computeBoundingSphere();return g;
}
