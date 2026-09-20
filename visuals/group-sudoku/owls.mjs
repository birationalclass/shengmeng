import * as T from '../3d/vendor/three.module.js';
const TAU=Math.PI*2;
export function owlPose(time,index=0){
 const q=time*(.14+index*.013)+index*TAU/3;
 // Low flight outside the castle perimeter also clears the board in projection.
 return {x:Math.sin(q)*14.4,z:Math.cos(q)*13.8,y:2.8+Math.sin(q*2+index)*.25,
  heading:Math.atan2(Math.cos(q)*14.4,-Math.sin(q)*13.8),bank:Math.sin(q)*.13,
  flap:Math.sin(time*5.8+index*1.8)*.52*(Math.sin(time*.43+index)>.1?1:.12)};
}
export function installOwls(a,p){
 a.owls??=[];const ivory=new T.MeshStandardMaterial({color:0xf0e8d7,roughness:.88}),tan=new T.MeshStandardMaterial({color:0xa78964,roughness:.9}),tip=new T.MeshStandardMaterial({color:0x605647}),eye=new T.MeshStandardMaterial({color:0x171b1d}),beak=new T.MeshStandardMaterial({color:0xc79c49});
 const sphere=new T.SphereGeometry(1,10,8),feather=new T.CapsuleGeometry(.09,.53,3,6);
 const ellipsoid=(g,s,pos,m)=>{const o=a.mesh(g,sphere,m,pos);o.scale.set(...s);return o;};
 for(let i=0;i<3;i++){
  const root=new T.Group();root.userData.landmark='flying-owl';p.add(root);const body=new T.Group();root.add(body);const plumage=i===2?tan:ivory;
  ellipsoid(body,[.22,.22,.52],[0,0,0],plumage);ellipsoid(body,[.25,.26,.24],[0,.12,.38],plumage);
  for(const side of [-1,1]){ellipsoid(body,[.13,.16,.045],[side*.105,.14,.58],ivory);ellipsoid(body,[.052,.065,.032],[side*.105,.155,.621],eye);}
  const bill=a.mesh(body,new T.ConeGeometry(.055,.14,5),beak,[0,.07,.635]);bill.rotation.x=Math.PI/2;
  for(let j=-1;j<=1;j++){const tail=a.mesh(body,feather,plumage,[j*.095,-.03,-.56]);tail.rotation.x=Math.PI/2;tail.rotation.z=j*.12;tail.scale.set(.8,.8,.45);}
  const wings=[];
  for(const side of [-1,1]){const wing=new T.Group();body.add(wing);wing.position.set(side*.16,.035,0);ellipsoid(wing,[.66,.055,.29],[side*.50,0,-.09],plumage);
   for(let j=0;j<7;j++){const f=a.mesh(wing,feather,j>4?tip:plumage,[side*(.42+j*.105),0,-.26-j*.036]);f.rotation.x=Math.PI/2;f.rotation.z=-side*(.13+j*.11);f.scale.set(1,1-j*.055,.6);}wings.push(wing);}
  root.scale.setScalar(1.15);a.owls.push({root,body,wings,index:i});
 }
 updateOwls(a.owls,0,false);
}
export function updateOwls(owls,time,reduced=false){for(const o of owls||[]){const pose=owlPose(reduced?0:time,o.index);o.root.position.set(pose.x,pose.y,pose.z);o.root.rotation.y=pose.heading;o.body.rotation.z=reduced?0:pose.bank;o.wings[0].rotation.z=reduced?.12:pose.flap;o.wings[1].rotation.z=reduced?-.12:-pose.flap;}}
