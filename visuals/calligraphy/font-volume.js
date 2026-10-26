import * as T from './vendor/three.module.js';

const clamp=(x,a=0,b=1)=>Math.max(a,Math.min(b,x));
const smooth=x=>{x=clamp(x);return x*x*(3-2*x);};
const skew=-Math.tan(5*Math.PI/180)*1.08;
export const homepageDomain=1664,homepagePad=320;
export function homepagePoint(x,y){return [512+1.08*(x-512)+skew*(y-512),512+1.08*(y-512)];}
// These are the actual title SVG's optical transform and 18-unit round ink
// outline. Rendering paths directly avoids a platform font substitution.
export function paintHomepageGlyph(ctx,g,n,PathConstructor=Path2D){
 const s=n/homepageDomain,r=820/g.units;
 // The homepage SVG deliberately overflows its em box, especially above the
 // baseline. The 320-unit guard also covers the full 6,763-character family.
 ctx.clearRect(0,0,n,n);ctx.save();ctx.scale(s,s);ctx.translate(homepagePad,homepagePad);ctx.translate(512,512);ctx.transform(1.08,0,skew,1.08,0,0);ctx.translate(-512,-512);ctx.translate(512-g.advance*r/2,520);ctx.scale(r,-r);
 const path=new PathConstructor(g.path);ctx.fillStyle='#000';ctx.strokeStyle='#000';ctx.lineWidth=18/r;ctx.lineJoin='round';ctx.lineCap='round';ctx.stroke(path);ctx.fill(path);ctx.restore();
}
function edt1d(values,n){
 const out=new Float32Array(n),v=new Int32Array(n),z=new Float64Array(n+1);let k=0;v[0]=0;z[0]=-Infinity;z[1]=Infinity;
 for(let q=1;q<n;q++){let s;do{s=((values[q]+q*q)-(values[v[k]]+v[k]*v[k]))/(2*q-2*v[k]);if(s<=z[k])k--;else break;}while(k>=0);if(k<0){k=0;v[0]=q;z[0]=-Infinity;z[1]=Infinity;}else{k++;v[k]=q;z[k]=s;z[k+1]=Infinity;}}
 k=0;for(let q=0;q<n;q++){while(z[k+1]<q)k++;out[q]=(q-v[k])**2+values[v[k]];}return out;
}
function distances(mask,n,target){
 const temp=new Float32Array(n*n),result=new Float32Array(n*n),line=new Float32Array(n);
 for(let y=0;y<n;y++){for(let x=0;x<n;x++)line[x]=mask[y*n+x]===target?0:1e7;temp.set(edt1d(line,n),y*n);}
 for(let x=0;x<n;x++){for(let y=0;y<n;y++)line[y]=temp[y*n+x];const d=edt1d(line,n);for(let y=0;y<n;y++)result[y*n+x]=d[y];}return result;
}
function penSegments(medians,n){
 const segments=[];let clock=0;
 for(const points of medians||[]){
  const lengths=[0];for(let i=1;i<points.length;i++)lengths.push(lengths.at(-1)+Math.hypot(points[i][0]-points[i-1][0],points[i][1]-points[i-1][1]));
  const weight=Math.max(.25,Math.sqrt(lengths.at(-1)/400));
  for(let i=1;i<points.length;i++){
   const a=homepagePoint(points[i-1][0],900-points[i-1][1]).map(v=>(v+homepagePad)*n/homepageDomain),b=homepagePoint(points[i][0],900-points[i][1]).map(v=>(v+homepagePad)*n/homepageDomain);
   segments.push({a,b,start:clock+weight*lengths[i-1]/Math.max(1,lengths.at(-1)),end:clock+weight*lengths[i]/Math.max(1,lengths.at(-1))});
  }clock+=weight;
 }for(const s of segments){s.start/=clock;s.end/=clock;}return segments;
}
function penCoordinate(x,y,segments,n){
 if(!segments.length)return {birth:clamp(y/n),across:x/n};
 let best=Infinity,birth=0,across=0;
 for(const s of segments){const dx=s.b[0]-s.a[0],dy=s.b[1]-s.a[1],den=dx*dx+dy*dy,u=clamp(((x-s.a[0])*dx+(y-s.a[1])*dy)/Math.max(1e-8,den)),d=(x-s.a[0]-dx*u)**2+(y-s.a[1]-dy*u)**2;
  if(d<best){best=d;birth=s.start+(s.end-s.start)*u;across=((x-s.a[0])*dy-(y-s.a[1])*dx)/Math.sqrt(Math.max(1e-8,den))/32;}
 }return {birth:clamp(.015+.97*birth),across};
}
// Build a pair of curved height fields meeting on the *same* original outline.
// Width-dependent round bellies preserve counters and separated brush tips;
// there are no flat front plates, textured billboards or repeated extrusions.
export function meshFromAlpha(alpha,n,medians=[]){
 const mask=Uint8Array.from(alpha,v=>v>=128?1:0),inside=distances(mask,n,1),outside=distances(mask,n,0),field=Float32Array.from(inside,(v,i)=>Math.sqrt(outside[i])-Math.sqrt(v)),segments=penSegments(medians,n);
 const vertices=[],triangles=[],corners=new Map(),edges=new Map();
 const vertex=(x,y,d)=>{const pen=penCoordinate(x,y,segments,n),id=vertices.length;vertices.push({x:(x/n*homepageDomain-homepageDomain/2)/1024*3.18,y:(homepageDomain/2-y/n*homepageDomain)/1024*3.18,d:Math.max(0,d),birth:pen.birth,across:pen.across});return id;};
 const corner=id=>{if(!corners.has(id))corners.set(id,vertex(id%n+.5,Math.floor(id/n)+.5,field[id]));return corners.get(id);};
 const edge=(a,b)=>{const key=Math.min(a,b)+':'+Math.max(a,b);if(!edges.has(key)){const t=field[a]/(field[a]-field[b]);edges.set(key,vertex(a%n+.5+(b%n-a%n)*t,Math.floor(a/n)+.5+(Math.floor(b/n)-Math.floor(a/n))*t,0));}return edges.get(key);};
 const clip=ids=>{const poly=[];for(let j=0;j<3;j++){const a=ids[j],b=ids[(j+1)%3],yes=field[a]>0,next=field[b]>0;if(yes)poly.push(corner(a));if(yes!==next)poly.push(edge(a,b));}for(let j=1;j<poly.length-1;j++)triangles.push([poly[0],poly[j+1],poly[j]]);};
 for(let y=0;y<n-1;y++)for(let x=0;x<n-1;x++){const a=y*n+x,b=a+1,c=a+n,d=c+1;if(Math.max(field[a],field[b],field[c],field[d])<=0)continue;clip([a,b,d]);clip([a,d,c]);}
 for(const v of vertices)v.h=.25*Math.sqrt(1-Math.exp(-v.d/5.5));
 // Regularize the crown without moving a single contour vertex. A raw pixel
 // distance field produces tiny facets in metallic highlights at its medial
 // ridges; this constrained smoothing keeps the brush body fluid.
 const adjacent=vertices.map(()=>new Set());for(const tri of triangles)for(let i=0;i<3;i++){adjacent[tri[i]].add(tri[(i+1)%3]);adjacent[tri[i]].add(tri[(i+2)%3]);}
 for(let pass=0;pass<10;pass++){const heights=vertices.map(v=>v.h);vertices.forEach((v,i)=>{if(v.d<1e-7)return;let sum=0;for(const j of adjacent[i])sum+=heights[j];v.h=.55*heights[i]+.45*sum/Math.max(1,adjacent[i].size);});}
 if(!triangles.length)throw Error('该字体没有有效轮廓。');
 return {vertices,triangles,resolution:n,strokeCount:medians.length,source:'homepage-title-outline'};
}
export function prepareFontVolume(stroke,settings={}){return {...stroke,fullness:settings.fullness??1,depth:settings.depth??1,turn:settings.turn??1,motion:[0,1],gesture:{phases:[[0,'落锋'],[.12,'顺势成面'],[.88,'收锋']]}};}
function allocate(g,s){
 const base=s.mesh.vertices.length,capacity=base*2+s.mesh.triangles.length*6+8;
 g.setAttribute('position',new T.BufferAttribute(new Float32Array(capacity*3),3));g.setAttribute('normal',new T.BufferAttribute(new Float32Array(capacity*3),3));g.setAttribute('uv',new T.BufferAttribute(new Float32Array(capacity*2),2));g.setIndex(new T.BufferAttribute(new Uint32Array(s.mesh.triangles.length*18+18),1));
 g.userData.fontMesh=s.mesh;g.userData.top=new Uint32Array(base);g.userData.bottom=new Uint32Array(base);g.userData.L=0;g.userData.R=0;
}
export function updateFontVolume(g,s,progress,ridges=0,writing='flow'){
 if(g.userData.fontMesh!==s.mesh)allocate(g,s);
 const p=clamp(progress),a=g.attributes.position.array,uv=g.attributes.uv.array,index=g.index.array,{top,bottom}=g.userData,vertices=s.mesh.vertices;
 let used=0,indices=0;
 const add=(v,tip=false)=>{
  const mature=p>=.99999?1:writing==='reveal'?1:smooth((p-v.birth)/.035),h=v.h*s.fullness*(1+.004*ridges*Math.cos(v.across*12*Math.PI))*mature;
  const x=v.x+s.offset.x,y=v.y+s.offset.y,z=(.065*Math.sin(v.x*1.8+v.y*.7)+.025*s.turn*Math.sin(v.y*2.1))*s.depth;
  const put=height=>{const id=used++;a[id*3]=x;a[id*3+1]=y;a[id*3+2]=z+height;uv[id*2]=v.birth;uv[id*2+1]=.5+v.across*.15;return id;};
  const front=put(h),back=h<1e-8?front:put(-h*.72);return [front,back];
 };
 for(let i=0;i<vertices.length;i++){const pair=add(vertices[i]);top[i]=pair[0];bottom[i]=pair[1];}
 const cut=new Map(),partial=[];
 const at=(a,b)=>{const key=Math.min(a,b)+':'+Math.max(a,b);if(!cut.has(key)){const x=vertices[a],y=vertices[b],t=clamp((p-x.birth)/(y.birth-x.birth)),v={x:x.x+(y.x-x.x)*t,y:x.y+(y.y-x.y)*t,h:x.h+(y.h-x.h)*t,birth:p,across:x.across+(y.across-x.across)*t};cut.set(key,add(v,true));}return cut.get(key);};
 const face=(front,back)=>{for(let j=1;j<front.length-1;j++){index[indices++]=front[0];index[indices++]=front[j];index[indices++]=front[j+1];index[indices++]=back[0];index[indices++]=back[j+1];index[indices++]=back[j];}};
 for(const tri of s.mesh.triangles){
  if(p>=.99999||tri.every(id=>vertices[id].birth<=p)){face(tri.map(id=>top[id]),tri.map(id=>bottom[id]));continue;}
  if(tri.every(id=>vertices[id].birth>p))continue;
  const f=[],b=[];for(let j=0;j<3;j++){const a=tri[j],next=tri[(j+1)%3],yes=vertices[a].birth<=p,other=vertices[next].birth<=p;if(yes){f.push(top[a]);b.push(bottom[a]);}if(yes!==other){const pair=at(a,next);f.push(pair[0]);b.push(pair[1]);}}face(f,b);
 }
 // Zero unused triangles so computeVertexNormals never visits stale indices.
 index.fill(0,indices);g.index.needsUpdate=true;g.setDrawRange(0,indices);g.attributes.position.needsUpdate=true;g.attributes.uv.needsUpdate=true;g.computeVertexNormals();
 if(p>=.99999){a.fill(0,used*3);g.computeBoundingBox();g.computeBoundingSphere();}
 g.userData.activeVertices=used;g.userData.activeIndices=indices;return g;
}
export function prepareHomepageModel(glyph,settings){
 const parts=glyph.strokes.map((stroke,i)=>({stroke,kind:'font-volume',spec:prepareFontVolume(stroke,settings),sourceIndices:[i]}));
 return {parts,transfers:[],report:{revision:'homepage-rounded-outline-v1',method:'Original homepage outlines / closed width-dependent rounded volume / median-guided surface growth',originalFont:true,characters:glyph.text.length,renderedPieceCount:parts.length,overlaps:0,regions:0,maxLift:0,maxResidual:0,manualLensSegments:0,scope:'Font silhouettes and layout are original. Depth, curved surfaces and writing timing are reconstructed; not a recovered author animation.'}};
}
