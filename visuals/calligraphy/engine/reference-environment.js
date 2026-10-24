import * as T from '../vendor/three.module.js';

// Authored softbox panorama for the pale, broad studio reflections in the
// reference film. This is a local lighting fit, not the artist's HDRI file.
export function createReferenceEnvironment(renderer,variant='v8'){
 const width=768,height=384,pixels=new Float32Array(width*height*4);
 const smooth=(a,b,x)=>T.MathUtils.smoothstep(x,a,b),angle=(a,b)=>Math.atan2(Math.sin(a-b),Math.cos(a-b));
 const box=(yaw,pitch,cx,cy,wx,wy)=>1-smooth(0,.12,Math.max(Math.abs(angle(yaw,cx))-wx,Math.abs(pitch-cy)-wy));
 for(let y=0;y<height;y++)for(let x=0;x<width;x++){
  const yaw=(x/width-.5)*Math.PI*2,pitch=(y/height-.5)*Math.PI;
  let value=.24+.10*Math.max(0,Math.sin(pitch));
  if(variant==='v9'){
   const front=box(yaw,pitch,1.57,.05,.85,.80);
   value+=.90*front*Math.exp(-.5*(angle(yaw,1.57)/.62)**2);
   value+=2.1*box(yaw,pitch,2.12,.38,.12,.77);
  }else value+=1.8*box(yaw,pitch,1.57,.05,.58,.80);
  value+=1.4*box(yaw,pitch,-.33,.95,.9,.38);
  value+=.65*box(yaw,pitch,-2.31,.25,.65,.75);
  value*=1-.90*box(yaw,pitch,2.82,-.05,.22,.85);
  value*=1-.65*box(yaw,pitch,.19,-.16,.13,.70);
  const at=(y*width+x)*4;pixels[at]=value;pixels[at+1]=value;pixels[at+2]=value;pixels[at+3]=1;
 }
 const panorama=new T.DataTexture(pixels,width,height,T.RGBAFormat,T.FloatType);
 panorama.mapping=T.EquirectangularReflectionMapping;panorama.colorSpace=T.LinearSRGBColorSpace;panorama.needsUpdate=true;
 const pmrem=new T.PMREMGenerator(renderer),target=pmrem.fromEquirectangular(panorama);panorama.dispose();pmrem.dispose();return target;
}
