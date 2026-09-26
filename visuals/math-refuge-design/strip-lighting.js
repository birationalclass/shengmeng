import * as T from 'three';
export function segmentDistanceSq(p,a,b){const d=b.map((v,i)=>v-a[i]),l=d.reduce((s,v)=>s+v*v,0),t=Math.max(0,Math.min(1,d.reduce((s,v,i)=>s+(p[i]-a[i])*v,0)/Math.max(l,1e-9)));return d.reduce((s,v,i)=>s+(p[i]-a[i]-v*t)**2,0);}
// Static world-space irradiance field: camera motion never changes the lights.
// One filtered lookup per coastal fragment, no shadow pass or light-selection pop.
export function createStripLighting(sources){
 const size=512,r=14;
 const xs=sources.flatMap(s=>[s.a[0],s.b[0]]),zs=sources.flatMap(s=>[s.a[2],s.b[2]]);
 const x0=Math.min(...xs)-r,z0=Math.min(...zs)-r,dx=Math.max(...xs)+r-x0,dz=Math.max(...zs)+r-z0;
 const pixels=new Uint8Array(size*size*4);
 for(let y=0;y<size;y++)for(let x=0;x<size;x++){
  const p=[x0+(x+.5)/size*dx,0,z0+(y+.5)/size*dz];let energy=0;
  for(const s of sources){const d2=segmentDistanceSq(p,s.a,s.b),edge=Math.max(0,1-d2/(r*r));energy+=.5*edge*edge/(1+.035*d2);}
  const v=Math.round(255*Math.min(1,energy));pixels.set([v,v,v,255],(y*size+x)*4);
 }
 const map=new T.DataTexture(pixels,size,size);map.minFilter=map.magFilter=T.LinearFilter;map.generateMipmaps=false;map.needsUpdate=true;
 return {uniforms:{coastLightMap:{value:map},coastLightBounds:{value:new T.Vector4(x0,z0,dx,dz)}},update(){},dispose(){map.dispose();}};
}
