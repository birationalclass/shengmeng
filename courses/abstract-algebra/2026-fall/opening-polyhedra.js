/* Classification: https://www.maths.ed.ac.uk/cheltsov/pdf/lecture8x.pdf
 * Triangle groups: https://web.stevens.edu/algebraic/GTI/Files/2012-02-02-talk-Conder.pdf
 * Exact Platonic solids, sampled on polygonal faces and slender edge tubes.
 * The convex hull is computed from supporting planes, retaining polygon faces
 * rather than mistaking the triangulation diagonals for polyhedron edges.
 */
(function (host) {
  'use strict';
  const phi=(1+Math.sqrt(5))/2, TAU=2*Math.PI;
  const add=(a,b)=>a.map((x,i)=>x+b[i]);
  const sub=(a,b)=>a.map((x,i)=>x-b[i]);
  const mul=(a,t)=>a.map(x=>x*t);
  const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
  const cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]];
  const unit=a=>mul(a,1/Math.hypot(...a));
  const cubes=[];for(const x of [-1,1])for(const y of [-1,1])for(const z of [-1,1])cubes.push([x,y,z]);
  function cyclic(a,b){const out=[];for(const s of [-1,1])for(const t of [-1,1])out.push([0,s*a,t*b],[t*b,0,s*a],[s*a,t*b,0]);return out;}
  const descriptions=[
    {name:'正四面体',vertices:cubes.filter(p=>p[0]*p[1]*p[2]>0),expected:[4,6,4],polygon:3,group:'A₄',triangle:[2,3,3]},
    {name:'正六面体',vertices:cubes,expected:[8,12,6],polygon:4,group:'S₄',triangle:[2,3,4]},
    {name:'正八面体',vertices:[[1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1],[0,0,-1]],expected:[6,12,8],polygon:3,group:'S₄',triangle:[2,3,4]},
    {name:'正十二面体',vertices:[...cubes,...cyclic(1/phi,phi)],expected:[20,30,12],polygon:5,group:'A₅',triangle:[2,3,5]},
    {name:'正二十面体',vertices:cyclic(1,phi),expected:[12,30,20],polygon:3,group:'A₅',triangle:[2,3,5]}
  ];
  function hull(description){
    const vertices=description.vertices.map(unit),faces=[],seen=new Set(),edges=new Map();
    for(let i=0;i<vertices.length;i++)for(let j=i+1;j<vertices.length;j++)for(let k=j+1;k<vertices.length;k++){
      const raw=cross(sub(vertices[j],vertices[i]),sub(vertices[k],vertices[i]));if(Math.hypot(...raw)<1e-8)continue;
      let normal=unit(raw),height=dot(normal,vertices[i]);
      const distances=vertices.map(p=>dot(normal,p)-height);
      if(distances.some(d=>d>1e-8)&&distances.some(d=>d<-1e-8))continue;
      const ids=distances.flatMap((d,id)=>Math.abs(d)<1e-8?[id]:[]),key=ids.join(':');if(seen.has(key))continue;seen.add(key);
      if(height<0){normal=mul(normal,-1);height=-height;}
      const centre=mul(ids.map(id=>vertices[id]).reduce(add,[0,0,0]),1/ids.length);
      const u=unit(sub(vertices[ids[0]],centre)),v=cross(normal,u);
      ids.sort((a,b)=>Math.atan2(dot(sub(vertices[a],centre),v),dot(sub(vertices[a],centre),u))-Math.atan2(dot(sub(vertices[b],centre),v),dot(sub(vertices[b],centre),u)));
      faces.push({ids,normal,centre,height});
      ids.forEach((a,index)=>{const b=ids[(index+1)%ids.length];edges.set([Math.min(a,b),Math.max(a,b)].join(':'),[a,b]);});
    }
    const edgeList=[...edges.values()],lengths=edgeList.map(([a,b])=>Math.hypot(...sub(vertices[a],vertices[b])));
    const counts=[vertices.length,edgeList.length,faces.length];
    if(counts.some((n,i)=>n!==description.expected[i])||faces.some(f=>f.ids.length!==description.polygon)||Math.max(...lengths)-Math.min(...lengths)>1e-8)throw new Error('Invalid regular polyhedron: '+description.name);
    return {...description,vertices,faces,edges:edgeList,edgeLength:lengths[0]};
  }
  const solids=descriptions.map(hull);
  function rotate(p,index){
    const ax=[.18,.42,.22,.28,.13][index],ay=[.28,-.48,.43,.31,-.22][index],az=[.07,.02,-.08,.09,.04][index];
    const [x,y,z]=p,y1=y*Math.cos(ax)-z*Math.sin(ax),z1=y*Math.sin(ax)+z*Math.cos(ax);
    const x2=x*Math.cos(ay)+z1*Math.sin(ay),z2=-x*Math.sin(ay)+z1*Math.cos(ay);
    return [x2*Math.cos(az)-y1*Math.sin(az),x2*Math.sin(az)+y1*Math.cos(az),z2];
  }
  const quaternionProduct=(a,b)=>[
    a[3]*b[0]+a[0]*b[3]+a[1]*b[2]-a[2]*b[1],
    a[3]*b[1]-a[0]*b[2]+a[1]*b[3]+a[2]*b[0],
    a[3]*b[2]+a[0]*b[1]-a[1]*b[0]+a[2]*b[3],
    a[3]*b[3]-a[0]*b[0]-a[1]*b[1]-a[2]*b[2]
  ];
  function quaternionRotate(p,q){
    const t=mul(cross(q.slice(0,3),p),2);return add(p,add(mul(t,q[3]),cross(q.slice(0,3),t)));
  }
  function axisRotate(p,axis,angle){const q=[...mul(axis,Math.sin(angle/2)),Math.cos(angle/2)];return quaternionRotate(p,q);}
  // Inverse of the shader's Rz(roll) Rx(pitch) Ry(yaw), followed by inverse
  // object spin. Both picking and drag axes use the current rendered camera.
  function fromCamera(p,view,spin){
    p=axisRotate(p,[0,0,1],-view.angles[2]);p=axisRotate(p,[1,0,0],-view.angles[0]);p=axisRotate(p,[0,1,0],-view.angles[1]);
    return axisRotate(p,[0,0,1],-spin);
  }
  function screenRay(x,y,width,height,view,spin){
    const aspect=width/height,fit=Math.min(.68,aspect*.84)*view.zoom;
    const t=Math.max(0,Math.min(1,(aspect-.8)/.5)),centre=.05+.15*t*t*(3-2*t);
    const image=[(2*x/width-1)*aspect/fit,(1-2*y/height-centre)/fit];
    const perspective=view.perspective,eye=perspective>1e-5?[0,0,3.9/perspective]:[...image,1000];
    const origin=add(fromCamera(eye,view,spin),axisRotate(view.target,[0,0,1],-spin));
    const direction=unit(fromCamera(sub([...image,0],eye),view,spin));
    return {origin,direction};
  }
  function dragRotation(dx,dy,view,spin){
    const length=Math.hypot(dx,dy);return {axis:length?unit(fromCamera([dy,dx,0],view,spin)):[0,1,0],angle:length*.007};
  }
  function triangleHit(origin,direction,a,b,c){
    const e1=sub(b,a),e2=sub(c,a),h=cross(direction,e2),det=dot(e1,h);if(Math.abs(det)<1e-10)return Infinity;
    const s=sub(origin,a),u=dot(s,h)/det;if(u<0||u>1)return Infinity;
    const q=cross(s,e1),v=dot(direction,q)/det;if(v<0||u+v>1)return Infinity;
    const distance=dot(e2,q)/det;return distance>1e-8?distance:Infinity;
  }
  function sample(count){
    if(count%5)throw new RangeError('Use an equal particle budget for each solid');
    let seed=0x5011d;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
    const centres=[[-.61,.37,0],[0,.37,0],[.61,.37,0],[-.34,-.31,0],[.34,-.31,0]],radius=.265,points=[];
    solids.forEach((solid,index)=>{
      const triangles=[];let area=0;
      for(const face of solid.faces)for(let j=0;j<face.ids.length;j++){
        const a=face.centre,b=solid.vertices[face.ids[j]],c=solid.vertices[face.ids[(j+1)%face.ids.length]];
        area+=Math.hypot(...cross(sub(b,a),sub(c,a)))/2;triangles.push({a,b,c,normal:face.normal,end:area});
      }
      for(let i=0;i<count/5;i++){
        let p,n;
        if(i<count/5*.7){
          const choice=random()*area,t=triangles.find(t=>choice<t.end),u=Math.sqrt(random()),v=random();
          p=add(mul(t.a,1-u),add(mul(t.b,u*(1-v)),mul(t.c,u*v)));n=t.normal;
        }else{
          const [a,b]=solid.edges[Math.floor(random()*solid.edges.length)].map(id=>solid.vertices[id]),direction=unit(sub(b,a));
          const tangent=unit(cross(direction,Math.abs(direction[2])<.9?[0,0,1]:[0,1,0])),bitangent=cross(direction,tangent),angle=random()*TAU;
          n=add(mul(tangent,Math.cos(angle)),mul(bitangent,Math.sin(angle)));
          p=add(add(a,mul(sub(b,a),random())),mul(n,.012));
        }
        p=add(mul(rotate(p,index),radius),centres[index]);n=rotate(n,index);
        points.push([...p,...n,index]);
      }
    });
    points.sort((a,b)=>((Math.atan2(a[1],a[0])+TAU)%TAU)-((Math.atan2(b[1],b[0])+TAU)%TAU)||Math.hypot(a[0],a[1])-Math.hypot(b[0],b[1]));
    const positions=new Float32Array(count*3),normals=new Float32Array(count*3),flat=new Float32Array(count*2),solidIds=new Uint8Array(count);
    points.forEach((p,i)=>{positions.set(p.slice(0,3),3*i);normals.set(p.slice(3,6),3*i);flat.set(p.slice(0,2),2*i);solidIds[i]=p[6];});
    const basePositions=positions.slice(),baseNormals=normals.slice(),orientations=solids.map(()=>[0,0,0,1]);
    const members=solids.map((_,id)=>Array.from(solidIds).flatMap((value,i)=>value===id?[i]:[]));
    function apply(index){
      const centre=centres[index],[x,y,z,w]=orientations[index];
      const m=[1-2*(y*y+z*z),2*(x*y-z*w),2*(x*z+y*w),2*(x*y+z*w),1-2*(x*x+z*z),2*(y*z-x*w),2*(x*z-y*w),2*(y*z+x*w),1-2*(x*x+y*y)];
      for(const i of members[index]){
        const k=i*3,px=basePositions[k]-centre[0],py=basePositions[k+1]-centre[1],pz=basePositions[k+2]-centre[2];
        const nx=baseNormals[k],ny=baseNormals[k+1],nz=baseNormals[k+2];
        for(let a=0;a<3;a++){
          positions[k+a]=m[a*3]*px+m[a*3+1]*py+m[a*3+2]*pz+centre[a];
          normals[k+a]=m[a*3]*nx+m[a*3+1]*ny+m[a*3+2]*nz;
        }
        flat[i*2]=positions[k];flat[i*2+1]=positions[k+1];
      }
    }
    function rotateSolid(index,axis,angle){
      if(!Number.isInteger(index)||index<0||index>=5||!axis.every(Number.isFinite)||!Number.isFinite(angle))throw new RangeError('Invalid solid rotation');
      if(!angle||Math.hypot(...axis)<1e-10)return;
      const step=[...mul(unit(axis),Math.sin(angle/2)),Math.cos(angle/2)],q=quaternionProduct(step,orientations[index]);
      orientations[index]=mul(q,1/Math.hypot(...q));apply(index);
    }
    function pick(origin,direction){
      let nearest=Infinity,selected=-1;
      solids.forEach((solid,index)=>{
        const vertices=solid.vertices.map(p=>add(mul(quaternionRotate(rotate(p,index),orientations[index]),radius),centres[index]));
        for(const face of solid.faces)for(let i=1;i<face.ids.length-1;i++){
          const distance=triangleHit(origin,direction,vertices[face.ids[0]],vertices[face.ids[i]],vertices[face.ids[i+1]]);
          if(distance<nearest){nearest=distance;selected=index;}
        }
      });return selected;
    }
    return {positions,normals,flat,solidIds,centres,rotateSolid,pick,orientations:()=>orientations.map(q=>q.slice()),reset(){for(let i=0;i<5;i++){orientations[i]=[0,0,0,1];apply(i);}}};
  }
  host.CourseOpeningPolyhedra=Object.freeze({sample,solids,screenRay,dragRotation,evidence:()=>solids.map(s=>({name:s.name,vertices:s.vertices.length,edges:s.edges.length,faces:s.faces.length,faceSides:s.polygon,edgeLength:s.edgeLength,rotationGroup:s.group,triangle:s.triangle}))});
})(typeof window!=='undefined'?window:globalThis);
