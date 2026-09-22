import * as THREE from 'three';
import {BUILDING_SCALE as S,DECK_Y,GARDEN_PADS} from './site-layout.js';
// Shared falloff patches avoid a separate realtime shadow/light pass per lantern.
export function createPathLighting(scene,{box,beam,materials}){
  const {stone,steel,brass}=materials;
  const glow=new THREE.MeshStandardMaterial({color:'#f4deba',roughness:.9,emissive:'#ffe2ac',emissiveIntensity:.1});
  const pixels=new Uint8Array(128*128*4);
  for(let y=0;y<128;y++)for(let x=0;x<128;x++){const r=Math.hypot(x-63.5,y-63.5)/64;pixels.set([255,219,163,Math.round(Math.max(0,1-r)**2*96)],(y*128+x)*4);}
  const map=new THREE.DataTexture(pixels,128,128);map.needsUpdate=true;map.colorSpace=THREE.SRGBColorSpace;
  const pool=new THREE.MeshBasicMaterial({map,transparent:true,opacity:0,depthWrite:false,polygonOffset:true,polygonOffsetFactor:-1,toneMapped:false});
  const geometry=new THREE.PlaneGeometry(1,1),patches=[];
  const positions=[[-20,-20],[-20,18],[-3,20],[15,20],[16,-20],[-44,8],[-57,8],[-65,8],[-63,-17],[-63,-34],[-63,-48],[-47,-15],[-42,-21],[-51,-27],[-42,-37],[-39,24.5],[-26,24.5],[-24,35],[-35,31],[-7,38],[28,-12],[28,14],[52,-12],[52,14],[34,-24],[42,-18]];
  for(const [i,[x,z]] of positions.entries()){
    const y=DECK_Y,type=i%3;
    if(type===0){ // Hollow limestone niche with a deeply recessed luminous ceiling.
      box([x,y+.45,z-.19],[.72,.9,.10],stone);
      for(const dx of [-.31,.31])box([x+dx,y+.45,z],[.10,.9,.48],stone);
      box([x,y+.89,z],[.72,.12,.48],stone);box([x,y+.045,z],[.72,.09,.48],stone);
      box([x,y+.81,z+.025],[.45,.015,.30],glow);
      box([x,y+.22,z+.025],[.38,.02,.26],brass);
    }else if(type===1){ // Bronze bollard, shielded downward slot.
      box([x,y+.36,z],[.15,.72,.15],steel);box([x,y+.76,z],[.38,.055,.30],brass);
      box([x,y+.716,z],[.27,.016,.21],glow);
    }else{ // Slender offset lantern with opaque top and opal lower face.
      beam([x,y,z],[x,y+2.3,z],.025,steel);beam([x,y+2.3,z],[x+.42,y+2.3,z],.025,brass);
      box([x+.42,y+2.27,z],[.48,.10,.30],steel);box([x+.42,y+2.21,z],[.38,.015,.23],glow);
    }
    const patch=new THREE.Mesh(geometry,pool);patch.name='Lantern soft ground pool '+i;patch.rotation.x=-Math.PI/2;patch.position.set(x,DECK_Y+.063,z);patch.scale.set(type===2?4:2.5,type===2?4:2.5,1);scene.add(patch);patches.push(patch);
    const marker=new THREE.Object3D();marker.name='Platform path lantern '+i;marker.position.set(x,y,z);marker.userData.type=['stone-niche','bronze-bollard','slender-pole'][type];scene.add(marker);
  }
  for(const [a,b,c,d] of GARDEN_PADS){
    for(const z of [c,d])box([(a+b)/2,.08,z],[b-a,.022,.024],glow);
    for(const x of [a,b])box([x,.08,(c+d)/2],[.024,.022,d-c],glow);
  }
  return {material:glow,count:positions.length,update(day){glow.emissiveIntensity=.08+(1-day)*1.5;pool.opacity=(1-day)*.72;},dispose(){map.dispose();pool.dispose();glow.dispose();geometry.dispose();}};
}
