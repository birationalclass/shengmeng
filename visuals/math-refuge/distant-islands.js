import * as THREE from 'three';
import {BUILDING_SCALE as S,DISTANT_ISLANDS} from './site-layout.js?v=15-fixed-hall';
import {seaLevel} from './landscape-shape.js?v=15-fixed-hall';

// Original low-cost radial terrain meshes, kept far away from the campus.
// No land is added beneath the buildings and the due-east view stays open.
export function createDistantIslands(scene){
  const group=new THREE.Group();group.name='Distant offshore islands';
  const material=new THREE.MeshStandardMaterial({vertexColors:true,roughness:1,metalness:0,envMapIntensity:.15});
  const geometries=[];
  for(const island of DISTANT_ISLANDS){
    const segments=96,rings=26,p=[],colors=[],indices=[];
    for(let j=0;j<=rings;j++)for(let i=0;i<=segments;i++){
      const r=j/rings,a=i/segments*Math.PI*2,s=island.seed;
      const coast=1+.085*Math.sin(3*a+s)+.055*Math.sin(5*a-s*.7);
      const x=Math.cos(a)*r*coast,z=Math.sin(a)*r*coast;
      const peaks=.68+.19*r*Math.sin(3*a+r*4+s)+.13*r*Math.cos(5*a-r*3);
      const height=seaLevel-1.3+island.height*Math.pow(Math.max(0,1-r*r),1.65)*peaks;
      p.push(x*island.rx,height,z*island.rz);
      const color=new THREE.Color(height<seaLevel+1.2?'#a19d86':height<seaLevel+4?'#697264':'#405e49');
      color.multiplyScalar(.92+.08*Math.sin(x*18+z*12+s));colors.push(...color.toArray());
    }
    for(let j=0;j<rings;j++)for(let i=0;i<segments;i++){
      const a=j*(segments+1)+i,b=a+1,c=a+segments+1,d=c+1;
      indices.push(a,b,c,b,d,c);
    }
    const geometry=new THREE.BufferGeometry();geometry.setAttribute('position',new THREE.Float32BufferAttribute(p,3));geometry.setAttribute('color',new THREE.Float32BufferAttribute(colors,3));geometry.setIndex(indices);geometry.computeVertexNormals();
    const mesh=new THREE.Mesh(geometry,material);mesh.name='Distant island '+island.seed;
    mesh.position.set(island.x*S,0,island.z*S);mesh.scale.setScalar(S);mesh.userData={...island};
    mesh.castShadow=false;mesh.receiveShadow=false;group.add(mesh);geometries.push(geometry);
  }
  scene.add(group);
  return {group,dispose(){geometries.forEach(g=>g.dispose());material.dispose();}};
}
