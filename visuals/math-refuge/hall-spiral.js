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
 const cx=west-3.5,cz=south-2.65,bottom=.275*S,rise=DECK_Y*S+HALL.clearHeight+.20*S,top=bottom+rise;
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
  if(i%2===0||i===n-1)for(const rr of [inner+.08,outer-.08]){const p=point((a+b)/2,rr,y);box(p.x,y+.015,p.z,.085,.03,.085,steel);const t=(i+.5)/n,railY=bottom+rise*(t+(1-t)/n)+.95;bar(p,new T.Vector3(p.x,railY,p.z),.015,brass);}
 }
 // Continuous curved strings and handrails, sharing the original material objects.
 for(const rr of [inner+.08,outer-.08])for(const [lift,size,mat] of [[-.16,.065,steel],[.95,.025,brass],[.48,.012,brass]]){
   const points=Array.from({length:161},(_,i)=>point(start+sweep*i/160,rr,bottom+rise*(i/160+(1-i/160)/n)+lift));
   mesh(new T.TubeGeometry(new T.CatmullRomCurve3(points),160,size,8,false),mat);
 }
 const landingWest=west-SPIRAL.upperEdge,landingSouth=south+SPIRAL.upperEdge,landingZ=landingSouth-SPIRAL.landingDepth/2;
 const landingLeft=point(start+sweep,inner,top).x,landingWidth=landingWest-landingLeft,landingNorth=landingSouth-SPIRAL.landingDepth;
 const slabThickness=.475*S;
 const floor=box((landingLeft+landingWest)/2,top-slabThickness/2,landingZ,landingWidth,slabThickness,SPIRAL.landingDepth,[materials.edge,materials.edge,materials.terraceFloor||materials.stone,materials.edge,materials.edge,materials.edge]);
 floor.name='Landing continuous terrace floor';
 const stripMaterial=materials.terraceStrip||light,stripY=top-.03*S,stripHeight=.022*S,stripWidth=.018*S;
 for(const z of [landingNorth,landingSouth])box((landingLeft+landingWest)/2,stripY,z,landingWidth,stripHeight,stripWidth,stripMaterial).name='Landing perimeter light strip';
 box(landingLeft,stripY,landingZ,stripWidth,stripHeight,SPIRAL.landingDepth,stripMaterial).name='Landing perimeter light strip';
 const pos=floor.geometry.attributes.position,uv=floor.geometry.attributes.uv;for(let i=0;i<pos.count;i++)uv.setXY(i,(pos.getX(i)+floor.position.x-offset.x)/S*.08,(pos.getZ(i)+floor.position.z-offset.z)/S*.08);uv.needsUpdate=true;
 for(const z of [landingNorth,landingSouth])bar(new T.Vector3(landingLeft,top-.2,z),new T.Vector3(landingWest,top-.2,z),.07,steel);
 // Rebuild the upper perimeter with an opening at the south end of its west edge.
 const north=HALL.north*S+offset.z,east=HALL.east*S+offset.x,edge=.275*S-.08*S;
 const deckNorth=north-SPIRAL.upperEdge,deckEast=east+SPIRAL.upperEdge;
 for(const [x1,z1,x2,z2] of [[landingWest,deckNorth,deckEast,deckNorth],[deckEast,deckNorth,deckEast,landingSouth],[landingWest,landingSouth,deckEast,landingSouth],[landingWest,deckNorth,landingWest,landingNorth]])box((x1+x2)/2,stripY,(z1+z2)/2,Math.abs(x2-x1)||stripWidth,stripHeight,Math.abs(z2-z1)||stripWidth,stripMaterial).name='Upper terrace continuous perimeter strip';
 const guardPosts=new Set(),guardJoints=new Set();
 function guard(x1,z1,x2,z2,lower=false){
  const len=Math.hypot(x2-x1,z2-z1);if(len<.001)return;
  const count=Math.max(1,Math.ceil(len/1.4));
  for(let i=0;i<=count;i++){
   const x=T.MathUtils.lerp(x1,x2,i/count),z=T.MathUtils.lerp(z1,z2,i/count),key=x.toFixed(4)+','+z.toFixed(4);
   if(!guardPosts.has(key)){guardPosts.add(key);bar(new T.Vector3(x,top,z),new T.Vector3(x,top+.95,z),.015,brass);}
  }
  for(const lift of (lower?[.95,.48]:[.95])){
   bar(new T.Vector3(x1,top+lift,z1),new T.Vector3(x2,top+lift,z2),lift===.95?.025:.012,brass);
   for(const [x,z] of [[x1,z1],[x2,z2]]){const key=[x,z,lift].map(v=>v.toFixed(4)).join(',');if(!guardJoints.has(key)){guardJoints.add(key);const joint=mesh(new T.SphereGeometry(lift===.95?.025:.012,12,8),brass);joint.position.set(x,top+lift,z);}}
  }
  const m=box((x1+x2)/2,top+.46,(z1+z2)/2,len,.76,.028,glass);m.rotation.y=-Math.atan2(z2-z1,x2-x1);
 }
 guard(west-edge,north-edge,east+edge,north-edge);guard(east+edge,north-edge,east+edge,south+edge);guard(east+edge,south+edge,west-edge,south+edge);
 guard(west-edge,north-edge,west-edge,landingZ-.8);
 const railLeft=point(start+sweep,inner+.08,top).x,railRight=point(start+sweep,outer-.08,top).x,railSouth=south+edge;
 guard(railLeft,landingNorth,railLeft,railSouth,true);
 guard(railLeft,railSouth,west-edge,railSouth,true);
 guard(railRight,landingNorth,west-edge,landingNorth,true);
 group.userData={steps:n,riser:rise/n,clearWidth:w,entry:point(start,r,bottom).toArray(),entryLeft:point(start,inner,bottom).toArray(),southwestCorner:[west,bottom,south],exit:[landingWest-.25,top,landingZ],landingCorner:[landingWest,top,landingSouth],upperSouthwestCorner:[landingWest,top,landingSouth],landingBounds:[landingLeft,landingWest,landingSouth-SPIRAL.landingDepth,landingSouth],materialPreserved:true};
 return group;
}
