import assert from 'node:assert/strict';
import {makeProfileTexture} from './ocean-renderer.js';
import {DataUtils} from '../3d/vendor/three.module.js';
const texture=makeProfileTexture();
const {width,height,data}=texture.image;
const value=(x,y,c)=>DataUtils.fromHalfFloat(data[(y*width+x)*4+c]);
let folds=0, intersections=0;
function intersect(a,b,c,d){
 const cross=(p,q,r)=>(q[0]-p[0])*(r[1]-p[1])-(q[1]-p[1])*(r[0]-p[0]);
 return cross(a,b,c)*cross(a,b,d)<-1e-10&&cross(c,d,a)*cross(c,d,b)<-1e-10;
}
for(let y=0;y<height;y++){
 const points=[];
 for(let x=0;x<width;x++){
  for(let c=0;c<4;c++)assert(Number.isFinite(value(x,y,c)));
  assert(value(x,y,1)>=-.001);
  assert(value(x,y,2)>=0&&value(x,y,2)<=1);
  const px=x/(width-1)*20-10+value(x,y,0),py=value(x,y,1);
  if(x>0&&px<(x-1)/(width-1)*20-10+value(x-1,y,0))folds++;
  if(x%4===0)points.push([px,py]);
 }
 assert(Math.abs(value(0,y,0))<.001&&Math.abs(value(width-1,y,0))<.001);
 assert(Math.abs(value(0,y,1))<.001&&Math.abs(value(width-1,y,1))<.001);
 for(let i=0;i<points.length-1;i++)for(let j=i+2;j<points.length-1;j++)if(intersect(points[i],points[i+1],points[j],points[j+1]))intersections++;
}
assert(folds>0,'The curl must contain an actual overhang');
assert.equal(intersections,0,'The sampled wave cross-section must not cross itself');
console.log(JSON.stringify({sampledStages:height,samplesPerStage:width,foldedSegments:folds,selfIntersections:intersections,finite:true,flatSeams:true},null,2));
