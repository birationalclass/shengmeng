import * as T from '../3d/vendor/three.module.js';
import {BUILDING_SCALE as S,DECK_Y,HALL} from './site-layout.js';
export const SPIRAL={steps:32,radius:2.65,width:1.65,start:Math.PI/2,sweep:Math.PI*1.5};
export function createHallSpiral(scene,materials,offset){
 const {timber,steel,brass,light,glass}=materials,group=new T.Group();group.name='Hall southwest curved stair';scene.add(group);
 const west=HALL.west*S+offset.x,south=HALL.south*S+offset.z;
 const cx=west-3.5,cz=south-2.65,bottom=DECK_Y*S,rise=DECK_Y*S+HALL.clearHeight+.20*S,top=bottom+rise;
 const {steps:n,radius:r,width:w,start,sweep}=SPIRAL,inner=r-w/2,outer=r+w/2;
 const point=(a,r,y)=>new T.Vector3(cx+r*Math.cos(a),y,cz+r*Math.sin(a));
 function mesh(geometry,material){const m=new T.Mesh(geometry,material);m.castShadow=material!==light&&material!==glass;m.receiveShadow=true;group.add(m);return m;}
 function bar(a,b,radius,material){const d=b.clone().sub(a),m=mesh(new T.CylinderGeometry(radius,radius,d.length(),8),material);m.position.copy(a).add(b).multiplyScalar(.5);m.quaternion.setFromUnitVectors(new T.Vector3(0,1,0),d.normalize());return m;}
 function box(x,y,z,w,h,d,material){const m=mesh(new T.BoxGeometry(w,h,d),material);m.position.set(x,y,z);return m;}
 for(let i=0;i<n;i++){
  const a=start+sweep*i/n,b=start+sweep*(i+1)/n,y=bottom+rise*(i+1)/n;
  const shape=new T.Shape();shape.absarc(0,0,outer,a,b,false);shape.lineTo(inner*Math.cos(b),inner*Math.sin(b));shape.absarc(0,0,inner,b,a,true);shape.closePath();
  const geometry=new T.ExtrudeGeometry(shape,{depth:.13,bevelEnabled:false,curveSegments:5});geometry.rotateX(Math.PI/2);const step=mesh(geometry,timber);step.position.set(cx,y,cz);step.name='Curved timber tread '+(i+1);
  bar(point(a+.012,inner+.08,y+.008),point(a+.012,outer-.08,y+.008),.008,light);
  if(i%2===0||i===n-1)for(const rr of [inner+.08,outer-.08]){const p=point((a+b)/2,rr,y);box(p.x,y+.015,p.z,.085,.03,.085,steel);bar(p,p.clone().add(new T.Vector3(0,.96,0)),.015,brass);}
 }
 // Continuous curved strings and handrails, sharing the original material objects.
 for(const rr of [inner+.08,outer-.08])for(const [lift,size,mat] of [[-.16,.065,steel],[.98,.025,brass],[.5,.012,brass]]){
   const points=Array.from({length:161},(_,i)=>point(start+sweep*i/160,rr,bottom+rise*i/160+lift+.08));
   mesh(new T.TubeGeometry(new T.CatmullRomCurve3(points),160,size,8,false),mat);
 }
 const landingZ=cz+.65;
 box(west-.75,top-.13,landingZ,2.0,.26,1.6,timber);
 for(const z of [landingZ-.8,landingZ+.8])bar(new T.Vector3(west-1.75,top-.2,z),new T.Vector3(west+.25,top-.2,z),.07,steel);
 // Rebuild the upper perimeter with an opening at the south end of its west edge.
 const north=HALL.north*S+offset.z,east=HALL.east*S+offset.x,edge=.275*S-.08*S;
 function guard(x1,z1,x2,z2){const count=Math.ceil(Math.hypot(x2-x1,z2-z1)/1.4);for(let i=0;i<=count;i++){const x=T.MathUtils.lerp(x1,x2,i/count),z=T.MathUtils.lerp(z1,z2,i/count);bar(new T.Vector3(x,top,z),new T.Vector3(x,top+.95,z),.015,brass);}bar(new T.Vector3(x1,top+.95,z1),new T.Vector3(x2,top+.95,z2),.025,brass);const len=Math.hypot(x2-x1,z2-z1),m=box((x1+x2)/2,top+.46,(z1+z2)/2,len,.76,.028,glass);m.rotation.y=-Math.atan2(z2-z1,x2-x1);}
 guard(west-edge,north-edge,east+edge,north-edge);guard(east+edge,north-edge,east+edge,south+edge);guard(east+edge,south+edge,west-edge,south+edge);
 guard(west-edge,north-edge,west-edge,landingZ-.8);guard(west-edge,landingZ+.8,west-edge,south+edge);
 guard(west-1.75,landingZ+.8,west-edge,landingZ+.8);
 group.userData={steps:n,riser:rise/n,clearWidth:w,entry:point(start,r,bottom).toArray(),exit:[west-.25,top,landingZ],materialPreserved:true};
 return group;
}
