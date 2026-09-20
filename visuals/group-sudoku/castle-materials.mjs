import * as T from '../3d/vendor/three.module.js';
// Shared deterministic masonry: no external images or extra loading stage.
export function masonryTexture(roof=false){
 const size=128,data=new Uint8Array(size*size*4);
 for(let y=0;y<size;y++)for(let x=0;x<size;x++){
  const row=Math.floor(y/16),joint=y%16<1||(x+(row%2)*16)%32<1;
  const grain=((x*17+y*31+(x*y)%23)%17)-8,block=(Math.floor((x+(row%2)*16)/32)*11+row*7)%19;
  const value=joint?(roof?139:167):(roof?210:231)+grain-block;
  const i=(y*size+x)*4;data[i]=value;data[i+1]=value;data[i+2]=value;data[i+3]=255;
 }
 const tex=new T.DataTexture(data,size,size,T.RGBAFormat);tex.wrapS=tex.wrapT=T.RepeatWrapping;tex.repeat.set(2,2);tex.magFilter=T.LinearFilter;tex.minFilter=T.LinearMipmapLinearFilter;tex.generateMipmaps=true;tex.colorSpace=T.SRGBColorSpace;tex.needsUpdate=true;return tex;
}
