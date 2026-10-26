import {prepareFontVolume,updateFontVolume} from '../font-volume.js?v=21';
import * as T from '../vendor/three.module.js';
import {prepareStroke,updateStrokeGeometry} from './stroke-volume.js';
import {prepareRailStroke,createStrokeGeometry,updateRailGeometry} from './yang-volume.js';
import {guardRailBends} from './bend-guard.js';
import {updateBrushGeometry,smoothSectionJoinNormals} from './brush-surface.js?v=21';

export function prepareVolume(stroke,kind,fullness=1,depth=1){
 if(kind==='font-volume')return prepareFontVolume(stroke,{fullness,depth});
 if(kind==='centerline')return prepareStroke({...stroke,points:stroke.points.map(([x,y,z])=>[x,y,z*depth]),thickness:stroke.thickness.map(n=>n*fullness)});
 return guardRailBends(prepareRailStroke({...stroke,a:stroke.a.map(([x,y,z])=>[x,y,z*depth]),b:stroke.b.map(([x,y,z])=>[x,y,z*depth]),front:stroke.front.map(n=>n*fullness),back:stroke.back.map(n=>n*fullness)}));
}
export function createVolume(length=220,radial=72){
 if(length===0)return new T.BufferGeometry();
 const g=createStrokeGeometry(length,radial),uv=new Float32Array(g.attributes.position.count*2),{L,R}=g.userData;
 uv[1]=.5;uv[uv.length-2]=1;uv[uv.length-1]=.5;
 for(let j=1;j<L;j++)for(let k=0;k<R;k++){const n=(1+(j-1)*R+k)*2;uv[n]=j/L;uv[n+1]=k/R;}
 g.setAttribute('uv',new T.BufferAttribute(uv,2));return g;
}
export function updateVolume(g,s,kind,p,ridges=0,writing='flow'){
 if(kind==='font-volume')return updateFontVolume(g,s,p,ridges,writing);
 g.userData.deferNormals=!!(ridges>0&&s.runSegments);
 if(s.forceReveal)writing='reveal';
 if(s.brush||s.surfaceStyle==='lens')updateBrushGeometry(g,s,p,writing);else if(kind==='centerline')updateStrokeGeometry(g,s,p);else updateRailGeometry(g,s,p);
 if(ridges>0){
  const {L,R}=g.userData,a=g.attributes.position.array;
  // Real longitudinal bristle channels follow the section, keep the contour
  // rails intact and fade at the poles. The mesh remains closed.
  for(let j=1;j<L;j++){
   let x=0,y=0,z=0;const base=1+(j-1)*R,u=p*j/L;
   for(let k=0;k<R;k++){const n=(base+k)*3;x+=a[n];y+=a[n+1];z+=a[n+2];}x/=R;y/=R;z/=R;
   const fade=Math.min(1,(j-(s.stitchStart?1:0))/6,(L-j-(s.stitchEnd&&p>=.99999?1:0))/6);
   for(let k=0;k<R;k++){
    const n=(base+k)*3,theta=k/R*Math.PI*2;
    const q=1+(s.spatial?.075:.19)*ridges*fade*Math.cos((s.spatial?15:9)*theta+.14*Math.sin(u*6))*Math.sin(theta)**2;
    a[n]=x+(a[n]-x)*q;a[n+1]=y+(a[n+1]-y)*q;a[n+2]=z+(a[n+2]-z)*q;
   }
  }
  g.attributes.position.needsUpdate=true;g.computeVertexNormals();smoothSectionJoinNormals(g,s,p);g.computeBoundingBox();g.computeBoundingSphere();
 }
 return g;
}
