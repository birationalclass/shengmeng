const fs=require('fs'),vm=require('vm'),assert=require('assert');
const dir=require('node:path').join(__dirname,'../');
const ctx={};vm.createContext(ctx);vm.runInContext(fs.readFileSync(dir+'opening-topology.js','utf8'),ctx);vm.runInContext(fs.readFileSync(dir+'opening-polyhedra.js','utf8'),ctx);
const topo=ctx.CourseOpeningTopology,poly=ctx.CourseOpeningPolyhedra;
const rx=(p,a)=>[p[0],Math.cos(a)*p[1]-Math.sin(a)*p[2],Math.sin(a)*p[1]+Math.cos(a)*p[2]];
const ry=(p,a)=>[Math.cos(a)*p[0]+Math.sin(a)*p[2],p[1],-Math.sin(a)*p[0]+Math.cos(a)*p[2]];
const rz=(p,a)=>[Math.cos(a)*p[0]-Math.sin(a)*p[1],Math.sin(a)*p[0]+Math.cos(a)*p[1],p[2]];
const cam=(p,v)=>rz(rx(ry(p,v.angles[1]),v.angles[0]),v.angles[2]);
function project(p,v,w,h,spin){p=rz(p,spin);p=p.map((c,i)=>c-v.target[i]);const q=cam(p,v),aspect=w/h,t=Math.max(0,Math.min(1,(aspect-.8)/.5)),fit=Math.min(.68,aspect*.84)*v.zoom,den=1-v.perspective*q[2]/3.9;return [(.5+.5*q[0]*fit/aspect/den)*w,(.5-.5*(q[1]*fit/den+.05+.15*t*t*(3-2*t)))*h];}
function rect(w,h){return w/h>1&&h<540?{top:Math.max(82,.24*h),bottom:Math.min(h-48,.85*h)}:{top:Math.max(170,.27*h),bottom:Math.min(h-110,.80*h)};}
const data=topo.sample(72000);for(let i=0;i<2;i++)data.rotateObject(i,[.4,.7,.5],1.37);
let ok=0;
for(const [w,h]of[[1280,800],[1920,1080],[390,844],[844,390],[600,800]])for(const perspective of[0,1])for(const angles of[[-.14,0,0],[.1,.5,.025],[-.42,-.4,-.07]])for(const spin of[0]){
 const base={angles,perspective,zoom:2,target:[0,0,0]},v=topo.frame(base,{width:w,height:h,spin}),r=rect(w,h);
 assert(v.zoom>=1&&v.zoom<=3.4);assert(v.target.every(Number.isFinite));assert.equal(v.angles[0],angles[0]);assert.equal(v.angles[1],angles[1]);assert.equal(v.perspective,perspective);
 let minX=Infinity,maxX=-Infinity,minY=Infinity,maxY=-Infinity;
 for(let i=0;i<data.positions.length;i+=3){const p=project([...data.positions.subarray(i,i+3)],v,w,h,spin);minX=Math.min(minX,p[0]);maxX=Math.max(maxX,p[0]);minY=Math.min(minY,p[1]);maxY=Math.max(maxY,p[1]);}
 const inside=minX>=w*.05-1e-3&&maxX<=w*.95+1e-3&&minY>=r.top-1e-3&&maxY<=r.bottom+1e-3;
 assert(inside,'Rotating either enlarged object must preserve the reserved text margins');ok++;
 if(w===1280&&h===800&&angles[0]===-.14)assert(v.zoom>1.7,'Desktop topology view is substantially larger');
}
// Picking consumes the returned camera directly, with no independent scaling.
for(const [w,h]of[[1280,800],[390,844],[844,390]]){
 const spin=0,v=topo.frame({angles:[-.14,.1,.02],perspective:1,zoom:1,target:[0,0,0]},{width:w,height:h,spin});
 for(let id=0;id<2;id++){
  let hits=0;for(let i=0;i<data.objectIds.length&&hits<3;i+=37)if(data.objectIds[i]===id){const p=project([...data.positions.subarray(i*3,i*3+3)],v,w,h,spin),ray=poly.screenRay(p[0],p[1],w,h,v,spin);if(data.pick(ray.origin,ray.direction)===id)hits++;}
  assert.equal(hits,3,'Both enlarged figures retain pick hits');
 }
}
console.log('PASS: '+ok+' responsive camera cases, full rotated geometry inside margins, shared camera picking for both objects');
