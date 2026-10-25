import * as T from '../vendor/three.module.js';
import {profile} from './stroke-volume.js';
import {sampleRailSection} from './yang-volume.js';
import {brushHead} from './brush-gesture.js?v=19';

const cubic2=(a,b,c,d,t)=>{const v=1-t;return [0,1].map(i=>a[i]*v*v*v+3*b[i]*v*v*t+3*c[i]*v*t*t+d[i]*t*t*t);};
const continuousCaches=new WeakMap();
function continuousCache(s,R){
 let sizes=continuousCaches.get(s);if(!sizes){sizes=new Map();continuousCaches.set(s,sizes);}if(sizes.has(R))return sizes.get(R);
 const N=1800,frames=new Float64Array((N+1)*10),shape=new Float32Array((N+1)*R*2),h=.5522847498307936;
 for(let i=0;i<=N;i++){
  const q=sampleRailSection(s,i/N),at=i*10,w=q.width;q.a.toArray(frames,at);q.d.toArray(frames,at+3);q.n.toArray(frames,at+6);frames[at+9]=w;
  const a=[-.5*w,0],b=[.5*w,0],f=[(q.crown-.5)*w,q.front],k=[(q.rear-.5)*w,-q.back],quadrants=[[b,[b[0],q.front*h],[f[0]+(1-q.crown)*w*h,f[1]],f],[f,[f[0]-q.crown*w*h,f[1]],[a[0],q.front*h],a],[a,[a[0],-q.back*h],[k[0]-q.rear*w*h,k[1]],k],[k,[k[0]+(1-q.rear)*w*h,k[1]],[b[0],-q.back*h],b]];
  for(let v=0;v<R;v++){const t=v/R*4,xy=cubic2(...quadrants[Math.floor(t)],t%1),index=(i*R+v)*2;shape[index]=xy[0]+w*.5;shape[index+1]=xy[1]+q.camber*Math.sin(v/R*Math.PI*2)**2;}
 }
 const cache={N,R,frames,shape};sizes.set(R,cache);return cache;
}
// Cache the unchanged four-rail section field. The moving front still changes
// pressure, width and roll each frame, but no longer allocates a Vector3 for
// every vertex or re-evaluates all section splines on every frame.
function updateContinuousGeometry(g,s,progress,writing){
 const {L,R}=g.userData,p=T.MathUtils.clamp(progress,.00001,1),a=g.attributes.position.array,{N,frames,shape}=continuousCache(s,R),anchored=writing==='flow'&&s.gesture?.anchor==='a',motion={pressure:profile(s.gesture?.pressure||[1,1],p),roll:profile(s.gesture?.roll||[0,0],p)};
 sampleRailSection(s,0).center.toArray(a,0);const tip=sampleRailSection(s,p);(p<.99999&&anchored?tip.a:tip.center).toArray(a,a.length-3);
 for(let j=1;j<L;j++){
  const u=p*j/L,t=u*N,i=Math.min(N-1,Math.floor(t)),f=t-i,b0=i*10,b1=b0+10,lerp=offset=>frames[b0+offset]*(1-f)+frames[b1+offset]*f;
  let dx=lerp(3),dy=lerp(4),dz=lerp(5),dl=Math.hypot(dx,dy,dz);dx/=dl;dy/=dl;dz/=dl;
  let nx=lerp(6),ny=lerp(7),nz=lerp(8);const nl=Math.hypot(nx,ny,nz);nx/=nl;ny/=nl;nz/=nl;
  const width=lerp(9),originX=lerp(0)+(anchored?0:dx*width*.5),originY=lerp(1)+(anchored?0:dy*width*.5),originZ=lerp(2)+(anchored?0:dz*width*.5),flow=brushHead(s,p,u,writing,motion),c=Math.cos(flow.roll),sn=Math.sin(flow.roll),
   ax=dx*c+nx*sn,ay=dy*c+ny*sn,az=dz*c+nz*sn,bx=nx*c-dx*sn,by=ny*c-dy*sn,bz=nz*c-dz*sn,
   head=p<.99999?Math.sqrt(Math.max(0,1-Math.pow(1-Math.min(1,(p-u)/Math.min(.018,p*.20)),2))):1,sx=flow.spread*head,sy=flow.pressure*head;
  for(let v=0;v<R;v++){const k=(i*R+v)*2,k1=k+R*2,x=(shape[k]*(1-f)+shape[k1]*f-(anchored?0:width*.5))*sx,y=(shape[k+1]*(1-f)+shape[k1+1]*f)*sy,n=(1+(j-1)*R+v)*3;a[n]=originX+ax*x+bx*y;a[n+1]=originY+ay*x+by*y;a[n+2]=originZ+az*x+bz*y;}
 }
 g.attributes.position.needsUpdate=true;if(!g.userData.deferNormals){g.computeVertexNormals();g.computeBoundingBox();g.computeBoundingSphere();}return g;
}

// Internal closing caps should not shade the visible joint between strokes.
// Reapply this after optional bristle-channel geometry recomputes normals.
export function smoothSectionJoinNormals(g,s,p){
 const {L,R}=g.userData,normals=g.attributes.normal.array;
 for(const [edge,neighbor,active] of [[1,2,s.stitchStart],[L-1,L-2,s.stitchEnd&&p>=.99999]])if(active)for(let k=0;k<R;k++)for(let c=0;c<3;c++)normals[(1+(edge-1)*R+k)*3+c]=normals[(1+(neighbor-1)*R+k)*3+c];
 g.attributes.normal.needsUpdate=true;
}

// Four independently defined rails, connected with tangent cubic quarters.
// Width grows from boundary A. It is not a tube appearing from its centre.
function updateBoundaryBrushGeometry(g,s,progress,writing){
 if((s.runSegments||s.cursive)&&s.cacheSections!==false)return updateContinuousGeometry(g,s,progress,writing);
 const {L,R}=g.userData,positions=g.attributes.position.array,p=T.MathUtils.clamp(progress,.00001,1),h=.5522847498307936;
 sampleRailSection(s,0).center.toArray(positions,0);
 const tip=sampleRailSection(s,p);
 (p<.99999&&writing==='flow'&&s.gesture?.anchor==='a'?tip.a:tip.center).toArray(positions,positions.length-3);
 for(let j=1;j<L;j++){
  const includeStart=s.stitchStart?1:0,includeEnd=s.stitchEnd&&p>=.99999?1:0;
  const u=p*(j-includeStart)/(L-includeStart-includeEnd),q=sampleRailSection(s,u),flow=brushHead(s,p,u,writing),w=q.width;
  if(s.stitchStart){const blend=T.MathUtils.smootherstep(u,0,.07);flow.spread=T.MathUtils.lerp(1,flow.spread,blend);flow.pressure=T.MathUtils.lerp(1,flow.pressure,blend);flow.roll*=blend;}
  const a=[-.5*w,0],b=[.5*w,0],f=[(q.crown-.5)*w,q.front],k=[(q.rear-.5)*w,-q.back];
  const quadrants=[
   [b,[b[0],q.front*h],[f[0]+(1-q.crown)*w*h,f[1]],f],
   [f,[f[0]-q.crown*w*h,f[1]],[a[0],q.front*h],a],
   [a,[a[0],-q.back*h],[k[0]-q.rear*w*h,k[1]],k],
   [k,[k[0]+(1-q.rear)*w*h,k[1]],[b[0],-q.back*h],b]
  ];
  const across=q.d.clone().multiplyScalar(Math.cos(flow.roll)).addScaledVector(q.n,Math.sin(flow.roll)),normal=q.n.clone().multiplyScalar(Math.cos(flow.roll)).addScaledVector(q.d,-Math.sin(flow.roll));
  const head=p<.99999?Math.sqrt(Math.max(0,1-Math.pow(1-Math.min(1,(p-u)/Math.min(.018,p*.20)),2))):1;
  for(let v=0;v<R;v++){
   const theta=v/R*4,xy=cubic2(...quadrants[Math.floor(theta)],theta%1),camber=q.camber*Math.sin(v/R*Math.PI*2)**2;
   const anchored=writing==='flow'&&s.gesture?.anchor==='a';
   const point=(anchored?q.a:q.center).clone().addScaledVector(across,(xy[0]+(anchored ? .5*w : 0))*flow.spread*head).addScaledVector(normal,(xy[1]+camber)*flow.pressure*head);
   point.toArray(positions,(1+(j-1)*R+v)*3);
  }
 }
 g.attributes.position.needsUpdate=true;g.computeVertexNormals();
 smoothSectionJoinNormals(g,s,p);g.computeBoundingBox();g.computeBoundingSphere();return g;
}

// Closed asymmetric lens sections: a broad continuous face, soft rim and a
// separately shaped back. No periodic channels are baked into the surface.
export function updateBrushGeometry(g,s,progress=1,writing='flow'){
 if(s.boundaryLoft)return updateBoundaryBrushGeometry(g,s,progress,writing);
 const {L,R}=g.userData,positions=g.attributes.position.array,p=T.MathUtils.clamp(progress,.00001,1);
 sampleRailSection(s,0).center.toArray(positions,0);
 const anchored=writing==='flow'&&s.gesture?.inferred&&s.gesture.anchor==='a'&&p<.99999;
 const tip=sampleRailSection(s,p),tipHead=brushHead(s,p,p,writing);(anchored?tip.a:tip.center).clone().addScaledVector(tip.d,tipHead.shift*tip.width).toArray(positions,positions.length-3);
 for(let j=1;j<L;j++){
  const u=p*j/L,q=sampleRailSection(s,u),exponent=2/profile(s.sectionPower||[2.4,2.4],u),flow=brushHead(s,p,u,writing);
  const acrossAxis=q.d.clone().multiplyScalar(Math.cos(flow.roll)).addScaledVector(q.n,Math.sin(flow.roll)),normal=q.n.clone().multiplyScalar(Math.cos(flow.roll)).addScaledVector(q.d,-Math.sin(flow.roll));
  const head=p<.99999?Math.sqrt(Math.max(0,1-Math.pow(1-Math.min(1,(p-u)/Math.min(.024,p*.25)),2))):1;
  for(let k=0;k<R;k++){
   const theta=k/R*Math.PI*2,c=Math.cos(theta),v=Math.sin(theta),x=Math.sign(c)*Math.abs(c)**exponent,y=Math.sign(v)*Math.abs(v)**exponent;
   const arch=1-x*x,crown=v>=0?q.crown:q.rear;
   const across=q.width*(.5*x+(crown-.5)*arch)*flow.spread,height=((v>=0?q.front:q.back)*y+q.camber*arch)*flow.pressure;
   const point=(anchored?q.a:q.center).clone().addScaledVector(q.d,flow.shift*q.width).addScaledVector(acrossAxis,(across+(anchored?.5*q.width*flow.spread:0))*head).addScaledVector(normal,height*head);
   point.toArray(positions,(1+(j-1)*R+k)*3);
  }
 }
 g.attributes.position.needsUpdate=true;g.computeVertexNormals();g.computeBoundingBox();g.computeBoundingSphere();return g;
}
