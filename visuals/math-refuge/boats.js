import * as THREE from 'three';
import {BUILDING_SCALE as S,HALL} from './site-layout.js?v44-hall-clearance';
import {seaLevel} from './landscape-shape.js?v44-hall-clearance';
// Fixed offshore moorings; small bounded wave motion cannot drift through decks.
export function createBoats(scene){
  const root=new THREE.Group();root.name='Offshore sailboats and kayaks';scene.add(root);
  const geometries=[],materials=[],boats=[];
  const mat=(color,roughness=.7)=>{const m=new THREE.MeshStandardMaterial({color,roughness,metalness:.03,side:THREE.DoubleSide});materials.push(m);return m;};
  const cream=mat('#f2eddb'),canvas=mat('#e6d8b9',.95),teak=mat('#93724f'),metal=mat('#aab7b8',.4),dark=mat('#233d40'),red=mat('#b96343'),blue=mat('#507f8b');
  const geometry=g=>(geometries.push(g),g);
  function mesh(group,g,m,p=[0,0,0]){const o=new THREE.Mesh(geometry(g),m);o.position.fromArray(p);o.castShadow=true;group.add(o);return o;}
  function rod(group,a,b,r,m=metal){const av=new THREE.Vector3(...a),bv=new THREE.Vector3(...b),v=bv.clone().sub(av),o=mesh(group,new THREE.CylinderGeometry(r,r,v.length(),8),m,av.add(bv).multiplyScalar(.5).toArray());o.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),v.normalize());}
  function hull(length,width,depth){
    const p=[],indices=[],nx=24,nr=16;
    for(let i=0;i<=nx;i++){const t=i/nx,r=Math.pow(Math.sin(Math.PI*t),.65);for(let j=0;j<=nr;j++){const a=j/nr*Math.PI*2;p.push(Math.cos(a)*width*.5*r,Math.sin(a)*depth*r,(t-.5)*length);}}
    for(let i=0;i<nx;i++)for(let j=0;j<nr;j++){const a=i*(nr+1)+j,b=a+nr+1;indices.push(a,b,a+1,a+1,b,b+1);}
    const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(p,3));g.setIndex(indices);g.computeVertexNormals();return g;
  }
  function sail(group,a,b,c){
    const points=[],indices=[],n=12;
    // A rectangular parameter domain collapsed onto the triangle's top vertex.
    for(let i=0;i<=n;i++)for(let j=0;j<=n;j++){const u=i/n,v=j/n,w=(1-u)*v,t=(1-u)*(1-v);points.push(a[0]*t+b[0]*u+c[0]*w+.22*Math.sin(Math.PI*u)*Math.sin(Math.PI*v),a[1]*t+b[1]*u+c[1]*w,a[2]*t+b[2]*u+c[2]*w);}
    for(let i=0;i<n;i++)for(let j=0;j<n;j++){const k=i*(n+1)+j;indices.push(k,k+n+1,k+1,k+1,k+n+1,k+n+2);}
    const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(points,3));g.setIndex(indices);g.computeVertexNormals();mesh(group,g,canvas);
    rod(group,a,b,.011,cream);rod(group,b,c,.011,cream);rod(group,c,a,.011,cream);
  }
  function add(type,x,z,heading,index){
    const group=new THREE.Group();group.name=`${type==='sail'?'Small sailboat':'Sea kayak'} ${index+1}`;group.position.set(x*S,seaLevel*S+.04,z*S);group.rotation.y=heading;group.userData={type,mooring:[x,z],waterline:seaLevel*S};root.add(group);boats.push(group);
    if(type==='sail'){
      mesh(group,hull(5.4,1.65,.45),cream,[0,.03,0]);mesh(group,hull(4.8,1.37,.11),teak,[0,.34,0]);
      const cabin=mesh(group,new THREE.BoxGeometry(.98,.44,1.25),cream,[0,.61,-.1]);cabin.name='Low cabin';
      for(const side of [-1,1])mesh(group,new THREE.BoxGeometry(.012,.16,.7),dark,[side*.5,.66,-.1]);
      mesh(group,new THREE.BoxGeometry(.64,.025,.75),dark,[0,.465,1.25]);
      rod(group,[0,.34,-.65],[0,6,-.65],.035);rod(group,[0,1.05,-.65],[0,1.05,2.1],.027);
      sail(group,[0,1.1,-.61],[0,5.9,-.61],[0,1.15,2.05]);sail(group,[0,.9,-2.45],[0,5.35,-.71],[0,1.05,-.8]);
      for(const side of [-1,1])rod(group,[side*.61,.4,.15],[0,5.35,-.65],.007,metal);
    }else{
      mesh(group,hull(4.2,.66,.18),index%2?red:blue,[0,.045,0]);
      const cockpit=mesh(group,new THREE.SphereGeometry(1,20,10),dark,[0,.18,.15]);cockpit.scale.set(.23,.04,.48);
      const rim=mesh(group,new THREE.TorusGeometry(1,.07,6,28),cream,[0,.21,.15]);rim.rotation.x=Math.PI/2;rim.scale.set(.245,.50,.32);
      rod(group,[-.9,.28,.55],[.9,.28,-.55],.021,metal);
      for(const sign of [-1,1]){const blade=mesh(group,new THREE.SphereGeometry(1,12,6),cream,[sign*1.05,.28,-sign*.65]);blade.scale.set(.30,.025,.12);blade.rotation.y=.55;}
    }
  }
  [[75,85,.4],[-7,-85,-.7],[105,105,1.1]].forEach(([x,z,a],i)=>add('sail',x,z,a,i));
  // Facing east from the hall: 100 m ahead and 30 m to the right (south).
  add('sail',(HALL.west+HALL.east)/2+100/S,30/S,.55,3);
  boats.at(-1).name='Auditorium east sailboat';
  [[77,65,.35],[-17,65,-.8]].forEach(([x,z,a],i)=>add('kayak',x,z,a,i));
  let time=0;
  return {root,boats,update(dt,tide=seaLevel*S){time+=Math.max(0,Math.min(dt,.1));boats.forEach((boat,i)=>{boat.position.y=tide+.04+.055*Math.sin(time*.7+i*1.9);boat.rotation.z=.022*Math.sin(time*.6+i);boat.rotation.x=.012*Math.cos(time*.8+i);});},dispose(){geometries.forEach(g=>g.dispose());materials.forEach(m=>m.dispose());scene.remove(root);}};
}
