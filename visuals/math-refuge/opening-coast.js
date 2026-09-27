import {PerspectiveCamera,Vector3} from '../3d/vendor/three.module.js';
import {branchPoint} from '../ocean/elliptic-model.js';
import {OPENING_POSE} from './opening-camera.js';
import {fromBeach,COAST_LIFT} from './elliptic-site.js';
// Poster is captured at 1280 x 720. SVG uses the identical cover mapping.
export function openingCoast(){
 const camera=new PerspectiveCamera(OPENING_POSE.fov,1280/720,.1,30000);
 camera.position.fromArray(OPENING_POSE.position);camera.lookAt(...OPENING_POSE.target);camera.updateMatrixWorld();
 const points=[];
 // Geographic north is -Z, hence descending t traverses north to south.
 for(let i=0;i<=600;i++){
  const t=1.25-i*2.5/600,[bx,bz]=branchPoint(t),[px,pz]=branchPoint(t+.0001);
  const dx=px-bx,dz=pz-bz,length=Math.hypot(dx,dz);
  // Smooth presentation contour: omit sub-pixel sand relief from the loading stroke.
  const x=bx+dz/length*3,z=bz-dx/length*3;
  const [wx,wz]=fromBeach(x,z),v=new Vector3(wx,2.55+COAST_LIFT,wz).project(camera);
  const screen=[(v.x+1)*640,(1-v.y)*360];
  if(screen[0]>=12&&screen[0]<=1268)points.push({screen,world:[x,z]});
 }
 return points;
}
export const coastPath=()=>openingCoast().map((p,i)=>(i?'L':'M')+p.screen.map(v=>v.toFixed(2)).join(',')).join(' ');
