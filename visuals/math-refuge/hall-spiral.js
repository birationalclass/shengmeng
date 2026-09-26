import * as T from '../3d/vendor/three.module.js';
import {BUILDING_SCALE as S,DECK_Y,HALL} from './site-layout.js';
export const SPIRAL={steps:32,radius:2.65,width:1.65,landingDepth:1.6,upperEdge:.275*S,start:Math.PI/2,sweep:Math.PI*1.5};
// Anchor the inner/left entrance endpoint to the southwest wall corner; the opening extends south.
// The offset tapers to zero at the upper landing, preserving its existing connection.
export function spiralPlanPoint(west,south,t,radius=SPIRAL.radius){
 const u=Math.max(0,Math.min(1,t)),blend=1-u*u*(3-2*u),a=SPIRAL.start+SPIRAL.sweep*t;
 return [west-3.5+radius*Math.cos(a)+3.5*blend-SPIRAL.upperEdge*(1-blend),south-SPIRAL.radius+radius*Math.sin(a)+SPIRAL.width/2*blend+(SPIRAL.radius-SPIRAL.landingDepth+SPIRAL.upperEdge)*(1-blend)];
}
export function createHallSpiral(scene,materials,offset){
 const {timber,steel,brass,light,glass}=materials,group=new T.Group();group.name='Hall southwest curved stair';scene.add(group);
 const west=HALL.west*S+offset.x,south=HALL.south*S+offset.z;
 const cx=west-3.5,cz=south-2.65,bottom=DECK_Y*S,rise=DECK_Y*S+HALL.clearHeight+.20*S,top=bottom+rise;
 const {steps:n,radius:r,width:w,start,sweep}=SPIRAL,inner=r-w/2,outer=r+w/2;
 const point=(a,r,y)=>{const [x,z]=spiralPlanPoint(west,south,(a-start)/sweep,r);return new T.Vector3(x,y,z);};
 function mesh(geometry,material){const m=new T.Mesh(geometry,material);m.castShadow=material!==light&&material!==glass;m.receiveShadow=true;group.add(m);return m;}
 function bar(a,b,radius,material){const d=b.clone().sub(a),m=mesh(new T.CylinderGeometry(radius,radius,d.length(),8),material);m.position.copy(a).add(b).multiplyScalar(.5);m.quaternion.setFromUnitVectors(new T.Vector3(0,1,0),d.normalize());return m;}
 function box(x,y,z,w,h,d,material){const m=mesh(new T.BoxGeometry(w,h,d),material);m.position.set(x,y,z);return m;}
 for(let i=0;i<n;i++){
  const a=start+sweep*i/n,b=start+sweep*(i+1)/n,y=bottom+rise*(i+1)/n;
  const shape=new T.Shape();
  for(let j=0;j<=5;j++){const p=point(a+(b-a)*j/5,outer,0);if(j===0)shape.moveTo(p.x-cx,p.z-cz);else shape.lineTo(p.x-cx,p.z-cz);}
  for(let j=5;j>=0;j--){const p=point(a+(b-a)*j/5,inner,0);shape.lineTo(p.x-cx,p.z-cz);}shape.closePath();
  const geometry=new T.ExtrudeGeometry(shape,{depth:.13,bevelEnabled:false,curveSegments:5});geometry.rotateX(Math.PI/2);const step=mesh(geometry,timber);step.position.set(cx,y,cz);step.name='Curved timber tread '+(i+1);
  bar(point(a+.012,inner+.08,y+.008),point(a+.012,outer-.08,y+.008),.008,light);
  if(i%2===0||i===n-1)for(const rr of [inner+.08,outer-.08]){const p=point((a+b)/2,rr,y);box(p.x,y+.015,p.z,.085,.03,.085,steel);bar(p,p.clone().add(new T.Vector3(0,.96,0)),.015,brass);}
 }
 // Continuous curved strings and handrails, sharing the original material objects.
 for(const rr of [inner+.08,outer-.08])for(const [lift,size,mat] of [[-.16,.065,steel],[.98,.025,brass],[.5,.012,brass]]){
   const points=Array.from({length:161},(_,i)=>point(start+sweep*i/160,rr,bottom+rise*i/160+lift+.08));
   mesh(new T.TubeGeometry(new T.CatmullRomCurve3(points),160,size,8,false),mat);
 }
 const landingWest=west-SPIRAL.upperEdge,landingSouth=south+SPIRAL.upperEdge,landingZ=landingSouth-SPIRAL.landingDepth/2;
 box(landingWest-1,top-.13,landingZ,2.0,.26,SPIRAL.landingDepth,timber);
 for(const z of [landingZ-.8,landingZ+.8])bar(new T.Vector3(landingWest-2,top-.2,z),new T.Vector3(landingWest,top-.2,z),.07,steel);
 // Rebuild the upper perimeter with an opening at the south end of its west edge.
 const north=HALL.north*S+offset.z,east=HALL.east*S+offset.x,edge=.275*S-.08*S;
 function guard(x1,z1,x2,z2){const count=Math.ceil(Math.hypot(x2-x1,z2-z1)/1.4);for(let i=0;i<=count;i++){const x=T.MathUtils.lerp(x1,x2,i/count),z=T.MathUtils.lerp(z1,z2,i/count);bar(new T.Vector3(x,top,z),new T.Vector3(x,top+.95,z),.015,brass);}bar(new T.Vector3(x1,top+.95,z1),new T.Vector3(x2,top+.95,z2),.025,brass);const len=Math.hypot(x2-x1,z2-z1),m=box((x1+x2)/2,top+.46,(z1+z2)/2,len,.76,.028,glass);m.rotation.y=-Math.atan2(z2-z1,x2-x1);}
 guard(west-edge,north-edge,east+edge,north-edge);guard(east+edge,north-edge,east+edge,south+edge);guard(east+edge,south+edge,west-edge,south+edge);
 guard(west-edge,north-edge,west-edge,landingZ-.8);
 guard(landingWest-2,landingSouth,west-edge,landingSouth);
 group.userData={steps:n,riser:rise/n,clearWidth:w,entry:point(start,r,bottom).toArray(),entryLeft:point(start,inner,bottom).toArray(),southwestCorner:[west,bottom,south],exit:[landingWest-.25,top,landingZ],landingCorner:[landingWest,top,landingSouth],upperSouthwestCorner:[landingWest,top,landingSouth],landingBounds:[landingWest-2,landingWest,landingSouth-SPIRAL.landingDepth,landingSouth],materialPreserved:true};
 return group;
}
