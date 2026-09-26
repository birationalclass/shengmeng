import * as THREE from 'three';
// A translucent marking lying just above the roof, not a floating billboard.
export function createRoofNumber(scene,number,x,roofY,z,width,depth){
  const canvas=document.createElement('canvas');canvas.width=canvas.height=1024;
  const ctx=canvas.getContext('2d');ctx.fillStyle='#f3e4c7';
  ctx.font='600 820px Georgia, serif';ctx.textAlign='center';ctx.textBaseline='middle';
  ctx.fillText(String(number),512,552);
  const texture=new THREE.CanvasTexture(canvas);texture.colorSpace=THREE.SRGBColorSpace;texture.anisotropy=4;
  const size=Math.min(width,depth)*.85;
  const material=new THREE.MeshBasicMaterial({map:texture,transparent:true,opacity:.52,depthTest:true,depthWrite:false,toneMapped:false,polygonOffset:true,polygonOffsetFactor:-1,polygonOffsetUnits:-1});
  const mesh=new THREE.Mesh(new THREE.PlaneGeometry(size,size),material);
  mesh.name='Roof number '+number;mesh.rotation.x=-Math.PI/2;mesh.position.set(x,roofY+.025,z);
  mesh.userData.roofNumber=number;mesh.userData.roof={x,y:roofY,z,width,depth};scene.add(mesh);
  return {mesh,dispose(){mesh.geometry.dispose();material.dispose();texture.dispose();}};
}
