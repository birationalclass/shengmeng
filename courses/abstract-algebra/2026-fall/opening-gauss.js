/* Gauss's constructible regular 17-gon, with Richmond's compass/straightedge
 * construction behind it. All defining coordinates use field operations and
 * square roots; the arcs illustrate genuine circle intersections and transfers.
 * https://crypto.stanford.edu/pbc/notes/numbertheory/17gon.html
 * https://mathcircle.berkeley.edu/sites/default/files/BMC6/ps0506/Heptadecagon.pdf
 * Richmond, Quart. J. Pure Appl. Math. 26 (1893), 206–207.
 */
(function(host){
  'use strict';
  const TAU=2*Math.PI,R=.77;
  const x1=(-1+Math.sqrt(17))/2,x2=(-1-Math.sqrt(17))/2;
  const y1=(x1+Math.sqrt(x1*x1+4))/2,y3=(x2+Math.sqrt(x2*x2+4))/2;
  const cosine=(y1+Math.sqrt(y1*y1-4*y3))/4,sine=Math.sqrt(1-cosine*cosine);
  const vertices=[];let x=R,y=0;
  for(let i=0;i<17;i++){vertices.push([x,y,0]);[x,y]=[x*cosine-y*sine,x*sine+y*cosine];}
  const side=Math.hypot(vertices[1][0]-vertices[0][0],vertices[1][1]-vertices[0][1]);
  // J is one quarter of the vertical radius. Bisect ∠OJA twice to find E;
  // rotate JE by 45° toward the left to find F on the horizontal diameter.
  const half=4/(Math.sqrt(17)+1),quarter=half/(1+Math.sqrt(1+half*half));
  const e=quarter/4,f=(quarter-1)/(4*(quarter+1)),k=Math.sqrt(-f),rho=Math.hypot(e,k);
  const O=[0,0],A=[R,0],J=[0,R/4],E=[R*e,0],F=[R*f,0],K=[0,R*k];
  const N3=R*(e+rho),N5=R*(e-rho);
  const circles=[{centre:[R*(1+f)/2,0],radius:R*(1-f)/2},{centre:E,radius:R*rho}];
  function chordThrough(a,b){
    const dx=b[0]-a[0],dy=b[1]-a[1],aa=dx*dx+dy*dy,bb=2*(a[0]*dx+a[1]*dy),cc=a[0]*a[0]+a[1]*a[1]-R*R;
    const root=Math.sqrt(bb*bb-4*aa*cc),t1=(-bb-root)/(2*aa),t2=(-bb+root)/(2*aa);
    return [[a[0]+dx*t1,a[1]+dy*t1],[a[0]+dx*t2,a[1]+dy*t2]];
  }
  const lines=[
    [[-R*1.035,0],[R*1.035,0]],[[0,-R*1.035],[0,R*1.035]],
    chordThrough(J,A),chordThrough(J,E),chordThrough(J,F),chordThrough(J,[R*half/4,0]),[E,K],
    [[N3,-Math.sqrt(R*R-N3*N3)],[N3,Math.sqrt(R*R-N3*N3)]],
    [[N5,-Math.sqrt(R*R-N5*N5)],[N5,Math.sqrt(R*R-N5*N5)]],
    [A,vertices[3]],[A,vertices[5]]
  ];
  const weights=[],circleWeights=[];let total=0,circleTotal=0;
  for(const [a,b] of lines){total+=Math.hypot(b[0]-a[0],b[1]-a[1]);weights.push(total);}
  for(const c of circles){circleTotal+=c.radius;circleWeights.push(circleTotal);}
  const widths=Object.freeze({circumcircle:.009,polygon:.0017,auxiliaryCircle:.0011,auxiliaryLine:.00085,transferArc:.001});
  function sample(count){
    let seed=0x1796;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
    const points=[],componentCounts=[0,0,0,0,0,0];
    for(let i=0;i<count;i++){
      const fraction=i/count,phase=random()*TAU;let p,n,component;
      const tube=(x,y,tx,ty,r)=>{const l=Math.hypot(tx,ty),nx=-ty/l*Math.cos(phase),ny=tx/l*Math.cos(phase),nz=Math.sin(phase);return [[x+r*nx,y+r*ny,r*nz],[nx,ny,nz]];};
      if(fraction<.48){
        component=0;const a=random()*TAU;[p,n]=tube(R*Math.cos(a),R*Math.sin(a),-Math.sin(a),Math.cos(a),widths.circumcircle);
      }else if(fraction<.61){
        component=1;const id=Math.floor(random()*17),a=vertices[id],b=vertices[(id+1)%17],t=random();
        [p,n]=tube(a[0]+(b[0]-a[0])*t,a[1]+(b[1]-a[1])*t,b[0]-a[0],b[1]-a[1],widths.polygon);
      }else if(fraction<.71){
        component=2;const a=vertices[Math.floor(random()*17)],z=random()*2-1,r=Math.sqrt(1-z*z);n=[r*Math.cos(phase),r*Math.sin(phase),z];p=a.map((x,k)=>x+.008*n[k]);
      }else if(fraction<.85){
        component=3;const choice=random()*circleTotal,c=circles[circleWeights.findIndex(w=>choice<w)],a=random()*TAU;
        [p,n]=tube(c.centre[0]+c.radius*Math.cos(a),c.centre[1]+c.radius*Math.sin(a),-Math.sin(a),Math.cos(a),widths.auxiliaryCircle);
      }else if(fraction<.96){
        component=4;const choice=random()*total,[a,b]=lines[weights.findIndex(w=>choice<w)],t=random();
        [p,n]=tube(a[0]+(b[0]-a[0])*t,a[1]+(b[1]-a[1])*t,b[0]-a[0],b[1]-a[1],widths.auxiliaryLine);
      }else{
        component=5;const id=Math.floor(random()*17),a=vertices[id],b=vertices[(id+1)%17],base=Math.atan2(b[1]-a[1],b[0]-a[0]),t=base+(random()-.5)*.43;
        [p,n]=tube(a[0]+side*Math.cos(t),a[1]+side*Math.sin(t),-Math.sin(t),Math.cos(t),widths.transferArc);
      }
      componentCounts[component]++;points.push([...p,...n]);
    }
    points.sort((a,b)=>((Math.atan2(a[1],a[0])+TAU)%TAU)-((Math.atan2(b[1],b[0])+TAU)%TAU)||Math.hypot(a[0],a[1])-Math.hypot(b[0],b[1]));
    const positions=new Float32Array(count*3),normals=new Float32Array(count*3),flat=new Float32Array(count*2);
    points.forEach((p,i)=>{positions.set(p.slice(0,3),i*3);normals.set(p.slice(3),i*3);flat.set(p.slice(0,2),i*2);});
    return {positions,normals,flat,componentCounts};
  }
  host.CourseOpeningGauss=Object.freeze({sample,vertices:vertices.map(Object.freeze),cosine,sine,side,widths,
    construction:Object.freeze({O,A,J,E,F,K,N3,N5,circles,lines}),
    evidence:()=>({sides:17,radius:R,fermatPrime:17,year:1796,constructible:true,firstVertexMethod:'Gaussian periods; field operations and square roots',construction:'Richmond, 1893',widths,chord:side,closureError:Math.hypot(x-R,y)})});
})(typeof window!=='undefined'?window:globalThis);
