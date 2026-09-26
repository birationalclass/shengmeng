import * as THREE from 'three';
export function createOpenBook(){
  const book=new THREE.Group();book.name='Library open book sculpture';
  const paper=new THREE.MeshStandardMaterial({color:'#ece3c7',roughness:.85,side:THREE.DoubleSide});
  const cover=new THREE.MeshStandardMaterial({color:'#41625c',roughness:.65,metalness:.15,side:THREE.DoubleSide});
  const gold=new THREE.MeshStandardMaterial({color:'#b8a079',roughness:.7,metalness:.35});
  const owned=[];
  function leaf(side,y,material,extra=0){const p=[],uv=[],idx=[],n=20;for(let i=0;i<=n;i++){const t=i/n,x=side*(1.08+extra)*t,h=y+.23*t+.085*Math.sin(Math.PI*t);for(const z of [-.82-extra,.82+extra]){p.push(x,h,z);uv.push(t,z<0?0:1);}}for(let i=0;i<n;i++){const k=i*2;idx.push(k,k+1,k+2,k+2,k+1,k+3);}const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(p,3));g.setAttribute('uv',new THREE.Float32BufferAttribute(uv,2));g.setIndex(idx);g.computeVertexNormals();owned.push(g);const m=new THREE.Mesh(g,material);m.castShadow=true;m.receiveShadow=true;book.add(m);}
  for(const side of [-1,1]){leaf(side,0,cover,.055);for(let i=0;i<5;i++)leaf(side,.025+i*.017,paper);}
  const spineGeometry=new THREE.CylinderGeometry(.045,.045,1.77,12);owned.push(spineGeometry);const spine=new THREE.Mesh(spineGeometry,gold);spine.rotation.x=Math.PI/2;spine.position.y=.04;book.add(spine);
  // Fine raised rules suggest printed pages while keeping the sculpture quiet.
  for(const side of [-1,1])for(let i=0;i<8;i++){const x=side*.58,t=.58/1.08,y=.101+.23*t+.085*Math.sin(Math.PI*t)+.004,g=new THREE.BoxGeometry(.67,.007,.009);owned.push(g);const line=new THREE.Mesh(g,gold);line.position.set(x,y,-.52+i*.145);line.rotation.z=side*Math.atan(.23/1.08);book.add(line);}
  book.userData.openBook=true;
  return {book,dispose(){owned.forEach(g=>g.dispose());paper.dispose();cover.dispose();gold.dispose();}};
}
