import * as THREE from 'three';

// A continuous upholstered bucket back, bowed around the shoulders and
// reclining by 13 degrees. Shared geometry is instanced for every seat.
export function curvedSeatBack(upholstery=false){
  const nx=20,ny=10,positions=[],indices=[];
  for(let side=0;side<2;side++)for(let j=0;j<=ny;j++)for(let i=0;i<=nx;i++){
    const u=i/nx*2-1,t=j/ny;
    const half=upholstery?.46:.52,height=upholstery?.67:.78;
    positions.push(u*half,.60+(upholstery?.035:0)+t*height,
      -.30-.18*t+.17*u*u+(upholstery?.075:0)+(side===0?.035:-.035));
  }
  const layer=(nx+1)*(ny+1);
  for(let side=0;side<2;side++)for(let j=0;j<ny;j++)for(let i=0;i<nx;i++){
    const a=side*layer+j*(nx+1)+i,b=a+1,c=a+nx+1,d=c+1;
    indices.push(...(side===0?[a,b,c,b,d,c]:[a,c,b,b,c,d]));
  }
  const rim=[];
  for(let i=0;i<nx;i++)rim.push(i);
  for(let j=0;j<ny;j++)rim.push(j*(nx+1)+nx);
  for(let i=nx;i>0;i--)rim.push(ny*(nx+1)+i);
  for(let j=ny;j>0;j--)rim.push(j*(nx+1));
  for(let k=0;k<rim.length;k++){
    const a=rim[k],b=rim[(k+1)%rim.length];indices.push(a,a+layer,b,b,a+layer,b+layer);
  }
  const geometry=new THREE.BufferGeometry();geometry.name=upholstery?'Curved seat upholstery':'Reclined wraparound seat shell';
  geometry.setAttribute('position',new THREE.Float32BufferAttribute(positions,3));
  // The cloth repeats at a constant physical scale rather than stretching by row.
  const uv=[];for(let side=0;side<2;side++)for(let j=0;j<=ny;j++)for(let i=0;i<=nx;i++)uv.push(i/nx,j/ny);
  geometry.setAttribute('uv',new THREE.Float32BufferAttribute(uv,2));geometry.setIndex(indices);geometry.computeVertexNormals();
  return geometry;
}

// Low-contrast, mineral clouding: deliberately no polished marble highlights.
export function terraceStoneMap(){
  const size=256,data=new Uint8Array(size*size*4);
  for(let y=0;y<size;y++)for(let x=0;x<size;x++){
    const wave=Math.sin(x*.037+Math.sin(y*.029)*2.1)*1.8+Math.sin(y*.067+x*.014)*1.2;
    const grain=((x*73+y*151+x*y*7)%31)/31-0.5;
    const shade=Math.round(244+wave+grain*2.4),i=(y*size+x)*4;
    data[i]=shade;data[i+1]=shade;data[i+2]=shade;data[i+3]=255;
  }
  const map=new THREE.DataTexture(data,size,size,THREE.RGBAFormat);map.colorSpace=THREE.SRGBColorSpace;
  map.generateMipmaps=true;map.minFilter=THREE.LinearMipmapLinearFilter;map.magFilter=THREE.LinearFilter;map.needsUpdate=true;
  return map;
}
