/* A circle and a one-half-twist Möbius band, with independent rotations.
 * The thin circle tube is a rendering aid for S¹, not an additional surface.
 * Retraction M(u,v) -> M(u,(1-t)v): https://stanford.edu/class/math215b/Sol1.pdf
 */
(function(host){
  'use strict';
  const TAU=2*Math.PI,R=.31,W=.125,TUBE=.013;
  const centres=[[-.50,.02,0],[.49,.02,0]];
  const add=(a,b)=>a.map((x,i)=>x+b[i]),sub=(a,b)=>a.map((x,i)=>x-b[i]),mul=(a,t)=>a.map(x=>x*t);
  const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0),cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]];
  const unit=a=>mul(a,1/Math.hypot(...a));
  function product(a,b){return [...add(add(mul(b.slice(0,3),a[3]),mul(a.slice(0,3),b[3])),cross(a,b)),a[3]*b[3]-dot(a.slice(0,3),b.slice(0,3))];}
  function rotate(p,q){const t=mul(cross(q,p),2);return add(p,add(mul(t,q[3]),cross(q,t)));}
  function axis(p,a,t){return rotate(p,[...mul(a,Math.sin(t/2)),Math.cos(t/2)]);}
  function pose(p,id){return id===0?axis(p,[1,0,0],.22):axis(axis(axis(p,[1,0,0],.72),[0,1,0],-.24),[0,0,1],-.20);}
  function mobius(u,v){const c=Math.cos(u),s=Math.sin(u),h=Math.cos(u/2);return [(R+v*h)*c,(R+v*h)*s,v*Math.sin(u/2)];}
  function mobiusFrame(u,v){
    const c=Math.cos(u),s=Math.sin(u),h=Math.cos(u/2),k=Math.sin(u/2),r=R+v*h;
    const du=[-r*s-v*k*c/2,r*c-v*k*s/2,v*h/2],dv=[h*c,h*s,k];
    return {du,dv,normal:unit(cross(du,dv)),area:Math.hypot(...cross(du,dv))};
  }
  function circle(u,v){return [(R+TUBE*Math.cos(v))*Math.cos(u),(R+TUBE*Math.cos(v))*Math.sin(u),TUBE*Math.sin(v)];}
  function hit(o,d,a,b,c){
    const e=sub(b,a),f=sub(c,a),h=cross(d,f),det=dot(e,h);if(Math.abs(det)<1e-10)return Infinity;
    const s=sub(o,a),u=dot(s,h)/det;if(u<0||u>1)return Infinity;
    const q=cross(s,e),v=dot(d,q)/det;if(v<0||u+v>1)return Infinity;
    const t=dot(f,q)/det;return t>1e-8?t:Infinity;
  }
  function mesh(id){
    const us=128,vs=id?16:12,vertices=[],triangles=[];
    for(let i=0;i<=us;i++)for(let j=0;j<=vs;j++)vertices.push(pose(id?mobius(i/us*TAU,(j/vs*2-1)*W):circle(i/us*TAU,j/vs*TAU),id));
    for(let i=0;i<us;i++)for(let j=0;j<vs;j++){const a=i*(vs+1)+j,b=a+vs+1;triangles.push([a,b,a+1],[a+1,b,b+1]);}
    return {vertices,triangles};
  }
  function sample(count){
    if(!Number.isInteger(count)||count<2)throw new RangeError('A particle budget is required');
    let seed=0x51b1;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
    const points=[],circleCount=Math.round(count*.28);
    for(let i=0;i<count;i++){
      const id=i<circleCount?0:1;let u=random()*TAU,v,p,n;
      if(!id){v=random()*TAU;p=circle(u,v);n=[Math.cos(v)*Math.cos(u),Math.cos(v)*Math.sin(u),Math.sin(v)];}
      else{
        const choice=random();
        if(choice<.52){
          // Area weighting avoids accumulating grains along the inner rim.
          do{u=random()*TAU;v=(random()*2-1)*W;}while(random()*.45>mobiusFrame(u,v).area);
          p=mobius(u,v);n=mobiusFrame(u,v).normal;
          // A nonorientable band has two local sides; sample both for emission.
          if(random()<.5)n=mul(n,-1);
          p=add(p,mul(n,.001));
        }else{
          // One connected boundary, traversed once over 0 <= u < 4π.
          const boundary=choice<.90;u=random()*TAU*(boundary?2:1);v=boundary?W:0;
          const frame=mobiusFrame(u,v),a=random()*TAU,tangent=unit(frame.du),binormal=unit(cross(tangent,frame.normal));
          n=add(mul(frame.normal,Math.cos(a)),mul(binormal,Math.sin(a)));
          p=add(mobius(u,v),mul(n,boundary?.005:.003));
        }
      }
      points.push([...add(pose(p,id),centres[id]),...pose(n,id),id]);
    }
    points.sort((a,b)=>((Math.atan2(a[1],a[0])+TAU)%TAU)-((Math.atan2(b[1],b[0])+TAU)%TAU)||Math.hypot(a[0],a[1])-Math.hypot(b[0],b[1]));
    const positions=new Float32Array(count*3),normals=new Float32Array(count*3),flat=new Float32Array(count*2),objectIds=new Uint8Array(count),members=[[],[]];
    points.forEach((p,i)=>{positions.set(p.slice(0,3),3*i);normals.set(p.slice(3,6),3*i);flat.set(p.slice(0,2),2*i);objectIds[i]=p[6];members[p[6]].push(i);});
    const original=positions.slice(),baseNormals=normals.slice(),orientations=[[0,0,0,1],[0,0,0,1]],meshes=[mesh(0),mesh(1)];
    function apply(id){
      const centre=centres[id],[x,y,z,w]=orientations[id];
      const m=[1-2*(y*y+z*z),2*(x*y-z*w),2*(x*z+y*w),2*(x*y+z*w),1-2*(x*x+z*z),2*(y*z-x*w),2*(x*z-y*w),2*(y*z+x*w),1-2*(x*x+y*y)];
      for(const i of members[id]){
        const k=i*3,px=original[k]-centre[0],py=original[k+1]-centre[1],pz=original[k+2]-centre[2];
        const nx=baseNormals[k],ny=baseNormals[k+1],nz=baseNormals[k+2];
        for(let a=0;a<3;a++){
          positions[k+a]=m[a*3]*px+m[a*3+1]*py+m[a*3+2]*pz+centre[a];
          normals[k+a]=m[a*3]*nx+m[a*3+1]*ny+m[a*3+2]*nz;
        }
        flat[i*2]=positions[k];flat[i*2+1]=positions[k+1];
      }
    }
    function rotateObject(id,a,angle){
      if(!Number.isInteger(id)||id<0||id>1||a.length!==3||!a.every(Number.isFinite)||!Number.isFinite(angle))throw new RangeError('Invalid topology rotation');
      if(!angle||Math.hypot(...a)<1e-10)return;
      orientations[id]=unit(product([...mul(unit(a),Math.sin(angle/2)),Math.cos(angle/2)],orientations[id]));apply(id);
    }
    function pick(origin,direction){
      let nearest=Infinity,selected=-1;
      for(let id=0;id<2;id++){
        const q=orientations[id],inverse=[-q[0],-q[1],-q[2],q[3]],o=rotate(sub(origin,centres[id]),inverse),d=rotate(direction,inverse),m=meshes[id];
        for(const [a,b,c] of m.triangles){const t=hit(o,d,m.vertices[a],m.vertices[b],m.vertices[c]);if(t<nearest){nearest=t;selected=id;}}
      }return selected;
    }
    return {positions,normals,flat,objectIds,centres:centres.map(p=>p.slice()),rotateObject,pick,orientations:()=>orientations.map(q=>q.slice()),reset(){for(let i=0;i<2;i++){orientations[i]=[0,0,0,1];apply(i);}}};
  }
  host.CourseOpeningTopology=Object.freeze({sample,mobius,mobiusFrame,circle,pose,radius:R,halfWidth:W,
    evidence:()=>({objects:['S¹','Möbius band'],halfTwists:1,boundaryComponents:1,fundamentalGroups:['ℤ','ℤ'],retraction:'M(u,v) → M(u,(1−t)v)',circleTubeIsRenderingAid:true})});
})(typeof window!=='undefined'?window:globalThis);
