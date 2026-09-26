import * as T from 'three';
import {RoundedBoxGeometry} from './vendor/geometries/RoundedBoxGeometry.js';
// Instanced parts share geometry across all thirty seats; only changed matrices upload.
export function createSwivelChairs(scene,positions,{shell,cloth,metal,timber,backs},S){
 const root=new T.Group();root.name='Auditorium swivel chairs';scene.add(root);
 const parts=[],targets=[],owned=[],angles=positions.map(()=>0),goals=positions.map(()=>0),dummy=new T.Object3D(),pivot=new T.Object3D();
 const rubber=new T.MeshStandardMaterial({color:'#252b29',roughness:.96});
 const satin=new T.MeshStandardMaterial({color:'#8f8c80',metalness:.72,roughness:.38});
 const graphite=new T.MeshStandardMaterial({color:'#414542',metalness:.48,roughness:.5});
 const profile=points=>{const g=new T.LatheGeometry(points.map(([r,y])=>new T.Vector2(r,y)),64);owned.push(g);return g;};
 const cylinder=(a,b,h)=>{const g=new T.CylinderGeometry(a,b,h,32);owned.push(g);return g;};
 const rounded=(w,h,d)=>{const g=new RoundedBoxGeometry(w,h,d,2,Math.min(w,h,d)*.18);owned.push(g);return g;};
 function add(g,m,p=[0,0,0],r=[0,0,0],rotating=false){
  const mesh=new T.InstancedMesh(g,m,positions.length);mesh.castShadow=true;mesh.receiveShadow=true;mesh.name=rotating?'Rotating chair upper assembly':'Fixed machined swivel pedestal';root.add(mesh);
  parts.push({mesh,p,r,rotating});if(rotating)targets.push(mesh);return mesh;
 }
 // Low, radiused disc with a recessed rubber foot and a fine satin rim.
 add(cylinder(.326,.326,.012),rubber,[0,.006,0]);
 add(profile([[0,.012],[.316,.012],[.337,.015],[.345,.020],[.347,.026],[.345,.032],[.339,.037],[.31,.042],[.15,.046],[0,.046]]),graphite);
 add(profile([[.338,.030],[.345,.029],[.346,.031],[.344,.034],[.338,.036]]),satin);
 // Smooth integral socket, slim column and recessed swivel bearing.
 add(profile([[0,.045],[.13,.045],[.112,.051],[.094,.066],[.075,.09],[.067,.13],[.063,.29],[.068,.325],[.082,.345],[0,.345]]),satin);
 add(cylinder(.077,.077,.021),graphite,[0,.354,0]);
 add(cylinder(.072,.072,.024),rubber,[0,.376,0]);
 add(profile([[0,.383],[.073,.383],[.086,.389],[.11,.4],[.115,.41],[0,.414]]),satin);
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
 return {targets:[],setSunsetDirection(direction,active){
  const desired=active?Math.atan2(direction[0],direction[2])-Math.PI/2:0;
  const back=Math.min(...positions.map(p=>p[0]));
  positions.forEach((p,i)=>{if(p[0]===back)goals[i]=angles[i]+Math.atan2(Math.sin(desired-angles[i]),Math.cos(desired-angles[i]));});
 },update(dt){
  for(let i=0;i<angles.length;i++)if(Math.abs(goals[i]-angles[i])>.0001){angles[i]+= (goals[i]-angles[i])*(1-Math.exp(-dt*.38));write(i);}
 },dispose(){owned.forEach(g=>g.dispose());rubber.dispose();satin.dispose();graphite.dispose();parts.forEach(p=>p.mesh.dispose());}};
}
