/* Gauss's constructible regular 17-gon. The first vertex is obtained only
 * by field operations and square roots (Gaussian periods), not angle division.
 * https://crypto.stanford.edu/pbc/notes/numbertheory/17gon.html
 * The arcs illustrate equal-chord transfer after the side length is known.
 */
(function(host){
  'use strict';
  const TAU=2*Math.PI,R=.77;
  const x1=(-1+Math.sqrt(17))/2,x2=(-1-Math.sqrt(17))/2;
  const y1=(x1+Math.sqrt(x1*x1+4))/2,y3=(x2+Math.sqrt(x2*x2+4))/2;
  const cosine=(y1+Math.sqrt(y1*y1-4*y3))/4,sine=Math.sqrt(1-cosine*cosine);
  const vertices=[];let x=0,y=R;
  for(let i=0;i<17;i++){vertices.push([x,y,0]);[x,y]=[x*cosine-y*sine,x*sine+y*cosine];}
  const side=Math.hypot(vertices[1][0]-vertices[0][0],vertices[1][1]-vertices[0][1]);
  function sample(count){
    let seed=0x1796;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
    const points=[],componentCounts=[0,0,0,0,0];
    for(let i=0;i<count;i++){
      const f=i/count,angle=random()*TAU;let p,n,component;
      const tube=(x,y,tx,ty,r)=>{const l=Math.hypot(tx,ty),nx=-ty/l*Math.cos(angle),ny=tx/l*Math.cos(angle),nz=Math.sin(angle);return [[x+r*nx,y+r*ny,r*nz],[nx,ny,nz]];};
      if(f<.46){
        component=0;const id=Math.floor(random()*17),a=vertices[id],b=vertices[(id+1)%17],t=random();
        [p,n]=tube(a[0]+(b[0]-a[0])*t,a[1]+(b[1]-a[1])*t,b[0]-a[0],b[1]-a[1],.0045);
      }else if(f<.64){
        component=1;const a=random()*TAU;[p,n]=tube(R*Math.cos(a),R*Math.sin(a),-Math.sin(a),Math.cos(a),.002);
      }else if(f<.83){
        component=2;const a=vertices[Math.floor(random()*17)],z=random()*2-1,r=Math.sqrt(1-z*z);n=[r*Math.cos(angle),r*Math.sin(angle),z];p=a.map((x,k)=>x+.016*n[k]);
      }else if(f<.95){
        component=3;const a=vertices[Math.floor(random()*17)],t=Math.sqrt(random());[p,n]=tube(a[0]*t,a[1]*t,a[0],a[1],.0012);
      }else{
        component=4;const id=random()<.5?0:1,a=vertices[id],b=vertices[(id+1)%17],base=Math.atan2(b[1]-a[1],b[0]-a[0]),t=base+(random()-.5)*.72;
        [p,n]=tube(a[0]+side*Math.cos(t),a[1]+side*Math.sin(t),-Math.sin(t),Math.cos(t),.0017);
      }
      componentCounts[component]++;points.push([...p,...n]);
    }
    points.sort((a,b)=>((Math.atan2(a[1],a[0])+TAU)%TAU)-((Math.atan2(b[1],b[0])+TAU)%TAU)||Math.hypot(a[0],a[1])-Math.hypot(b[0],b[1]));
    const positions=new Float32Array(count*3),normals=new Float32Array(count*3),flat=new Float32Array(count*2);
    points.forEach((p,i)=>{positions.set(p.slice(0,3),i*3);normals.set(p.slice(3),i*3);flat.set(p.slice(0,2),i*2);});
    return {positions,normals,flat,componentCounts};
  }
  host.CourseOpeningGauss=Object.freeze({sample,vertices:vertices.map(Object.freeze),cosine,sine,side,
    evidence:()=>({sides:17,radius:R,fermatPrime:17,year:1796,constructible:true,firstVertexMethod:'Gaussian periods; field operations and square roots',chord:side,closureError:Math.hypot(x,y-R)})});
})(typeof window!=='undefined'?window:globalThis);
