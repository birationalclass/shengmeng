import * as THREE from 'three';

// Small, tileable, deterministic micro-detail maps. No full-size photo textures
// or additional downloads are needed for cloth, brushed metal and plaster.
export function createDetailMaps(anisotropy=4){
  const size=128,cloth=new Uint8Array(size*size*4),rough=new Uint8Array(size*size*4),metal=new Uint8Array(size*size*4),plaster=new Uint8Array(size*size*4);
  for(let y=0;y<size;y++)for(let x=0;x<size;x++){
    const i=(y*size+x)*4,noise=((x*1973+y*9277+x*y*17)%251)/250;
    const sx=Math.cos(x*Math.PI/2)*.16,sy=Math.cos(y*Math.PI/2)*.16,n=1/Math.sqrt(1+sx*sx+sy*sy);
    cloth.set([(sx*n*.5+.5)*255,(sy*n*.5+.5)*255,(n*.5+.5)*255,255],i);
    const weave=215+noise*25+Math.sin((x+y)*Math.PI/2)*10;rough.set([weave,weave,weave,255],i);
    const brush=150+25*Math.sin(x*.7)+noise*22;metal.set([brush,brush,brush,255],i);
    plaster.set([126+noise*4,126+((x*31+y*13)%19)/19*4,255,255],i);
  }
  const make=(data,repeat)=>{
    const texture=new THREE.DataTexture(data,size,size,THREE.RGBAFormat);texture.wrapS=texture.wrapT=THREE.RepeatWrapping;
    texture.repeat.set(...repeat);texture.magFilter=THREE.LinearFilter;texture.minFilter=THREE.LinearMipmapLinearFilter;
    texture.generateMipmaps=true;texture.anisotropy=Math.min(4,anisotropy);texture.needsUpdate=true;return texture;
  };
  return {clothNormal:make(cloth,[12,12]),clothRoughness:make(rough,[12,12]),brushedRoughness:make(metal,[2,6]),plasterNormal:make(plaster,[5,5])};
}
export function isDistantVegetation(x,z){return x*x+z*z>60*60;}
