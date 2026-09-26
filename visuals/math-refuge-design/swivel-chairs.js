import * as T from 'three';
import {RoundedBoxGeometry} from './vendor/geometries/RoundedBoxGeometry.js';
// Instanced parts share geometry across all thirty seats; only changed matrices upload.
export function createSwivelChairs(scene,positions,{shell,cloth,metal,timber,backs},S){
 const root=new T.Group();root.name='Auditorium swivel chairs';scene.add(root);
 const parts=[],targets=[],owned=[],angles=positions.map(()=>0),goals=positions.map(()=>0),dummy=new T.Object3D(),pivot=new T.Object3D();
 const rubber=new T.MeshStandardMaterial({color:'#252b29',roughness:.96});
 const cylinder=(a,b,h)=>{const g=new T.CylinderGeometry(a,b,h,32);owned.push(g);return g;};
 const rounded=(w,h,d)=>{const g=new RoundedBoxGeometry(w,h,d,2,Math.min(w,h,d)*.18);owned.push(g);return g;};
 function add(g,m,p=[0,0,0],r=[0,0,0],rotating=false){
  const mesh=new T.InstancedMesh(g,m,positions.length);mesh.castShadow=true;mesh.receiveShadow=true;mesh.name=rotating?'Rotating chair upper assembly':'Fixed machined swivel pedestal';mesh.userData.designGroups=positions.map((_,i)=>'chair-'+i);root.add(mesh);
  parts.push({mesh,p,r,rotating});if(rotating)targets.push(mesh);return mesh;
 }
 add(cylinder(.35,.38,.036),rubber,[0,.018,0]);
 add(cylinder(.33,.365,.044),metal,[0,.052,0]);
 add(cylinder(.20,.30,.045),metal,[0,.096,0]);
 add(cylinder(.078,.13,.24),metal,[0,.236,0]);
 add(cylinder(.09,.09,.035),rubber,[0,.367,0]);
 add(cylinder(.105,.105,.025),metal,[0,.389,0]);
 for(let i=0;i<4;i++){const a=i*Math.PI/2+Math.PI/4;add(cylinder(.014,.014,.008),metal,[Math.cos(a)*.265,.078,Math.sin(a)*.265]);}
 add(rounded(.58,.05,.47),metal,[0,.416,.015],[0,0,0],true);
 add(rounded(1.04,.11,.83),shell,[0,.45,.03],[0,0,0],true);
 add(rounded(.96,.18,.77),cloth,[0,.53,.06],[.035,0,0],true);
 for(const [i,g] of backs.entries())add(g,i?cloth:shell,[0,0,0],[0,0,0],true);
 for(const sign of [-1,1]){
  add(rounded(.055,.065,.56),metal,[sign*.51,.70,0],[0,0,0],true);
  add(rounded(.12,.11,.51),cloth,[sign*.51,.75,.04],[0,0,0],true);
 }
 add(rounded(.035,.30,.32),timber,[.57,.79,-.07],[0,0,0],true);
 function write(i,all=false){
  const [x,y,z]=positions[i];pivot.position.set(x,y,z);pivot.rotation.set(0,Math.PI/2+angles[i],0);pivot.scale.setScalar(1/S);pivot.updateMatrix();
  for(const part of parts){if(!all&&!part.rotating)continue;
   dummy.position.fromArray(part.p);dummy.rotation.set(...part.r);dummy.scale.setScalar(1);dummy.updateMatrix();
   part.mesh.setMatrixAt(i,new T.Matrix4().multiplyMatrices(pivot.matrix,dummy.matrix));part.mesh.instanceMatrix.needsUpdate=true;
  }
 }
 positions.forEach((_,i)=>write(i,true));parts.forEach(p=>{p.mesh.computeBoundingSphere();p.mesh.boundingSphere.radius+=1;});
 return {targets,turn(index){if(Number.isInteger(index)&&index>=0&&index<goals.length)goals[index]+=Math.PI/4;},update(dt){
  for(let i=0;i<angles.length;i++)if(Math.abs(goals[i]-angles[i])>.0001){angles[i]+= (goals[i]-angles[i])*(1-Math.exp(-dt*5));write(i);}
 },dispose(){owned.forEach(g=>g.dispose());rubber.dispose();parts.forEach(p=>p.mesh.dispose());}};
}
