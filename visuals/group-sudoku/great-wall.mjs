import * as T from '../3d/vendor/three.module.js';
import {jointMotion} from './architectural-motion.mjs?v=living1';

export function banner(a,parent,x,y,z,phase=0){
 const mast=new T.Group();mast.position.set(x,y,z);parent.add(mast);
 a.rod(mast,[0,0,0],[0,1.55,0],.035,a.materials.brass);
 a.mesh(mast,new T.SphereGeometry(.085,8,6),a.materials.gold,[0,1.57,0]);
 const fabric=a.materials.red.clone();fabric.side=T.DoubleSide;
 let previous= new T.Group();mast.add(previous);previous.position.y=1.30;
 for(let i=0;i<5;i++){
  const fold=new T.Group();previous.add(fold);fold.position.x=i===0?0:.17;
  a.mesh(fold,new T.PlaneGeometry(.18,.44-i*.035),fabric,[.085,-.16,0]);
  jointMotion(a,fold,{axis:'y',speed:1.8,amplitude:.22,phase:phase-i*.65});previous=fold;
 }
 return mast;
}

export function greatWall(a,parent){
 a.wallBeacons=[];const wall=new T.Group();wall.name='Great Wall · 万里长城';wall.userData.landmark='great-wall';parent.add(wall);
 const stone=a.materials.stone.clone();stone.color.setHex(0x9b947d);
 const cap=a.materials.paper.clone();cap.color.setHex(0xb8ad91);
 const mortar=a.materials.dark.clone();mortar.color.setHex(0x645f50);
 const at=q=>{const radius=11.35+.12*Math.cos(q*8);return new T.Vector3(Math.sin(q)*radius,0,-Math.cos(q)*radius);};
 // A closed ring; the southern parapet stays lower to preserve the playing view.
 for(let i=0;i<64;i++){
  const q0=i*Math.PI*2/64,q1=(i+1)*Math.PI*2/64,p=at(q0),r=at(q1),d=r.clone().sub(p),len=d.length()+.045;
  const h=.55+2.00*(1+Math.cos((q0+q1)/2))/2;
  const segment=new T.Group();segment.userData.wallSegment={start:q0,end:q1,height:h};segment.position.copy(p.add(r).multiplyScalar(.5));segment.rotation.y=Math.atan2(d.x,d.z);wall.add(segment);
  a.box(segment,[1.03,h,len],[0,h/2+.15,0],stone);
  a.box(segment,[1.14,.12,len],[0,h+.20,0],cap);
  for(const side of [-1,1]){
   a.box(segment,[.16,.46,len],[side*.57,h+.48,0],stone);
   for(const z of [-len*.32,len*.32])a.box(segment,[.22,.34,.22],[side*.57,h+.88,z],cap);
   for(let row=0;row<Math.max(1,Math.floor(h/.37));row++){
    const y=.38+row*.37;a.box(segment,[.012,.015,len-.02],[side*.52,y,0],mortar);
    a.box(segment,[.012,.32,.018],[side*.525,y+.18,(row%2?1:-1)*len*.22],mortar);
   }
  }
  // Stone treads make the changing walkway height read as a walkable ramp.
  for(const z of [-len*.25,len*.25])a.box(segment,[.88,.022,.026],[0,h+.275,z],mortar);
 }
 for(const [j,q] of Array.from({length:8},(_,i)=>i*Math.PI/4).entries()){
  const p=at(q),tower=new T.Group();tower.position.copy(p);tower.rotation.y=-q;wall.add(tower);
  tower.userData.landmark='great-wall-watchtower';const h=1.20+2.20*(1+Math.cos(q))/2,w=1.45;
  a.box(tower,[w+.3,.25,w+.3],[0,.25,0],cap);
  a.box(tower,[w,h,w],[0,h/2+.35,0],stone);
  for(let y=.7;y<h+.2;y+=.43)for(const side of [-1,1]){
   a.box(tower,[w,.018,.014],[0,y,side*(w/2+.008)],mortar);
   a.box(tower,[.014,.018,w],[side*(w/2+.008),y,0],mortar);
  }
  for(const side of [-1,1])for(const x of [-.43,.43]){
   a.box(tower,[.20,.51,.022],[x,h-.42,side*(w/2+.018)],a.materials.dark);
   a.box(tower,[.30,.08,.06],[x,h-.73,side*(w/2+.05)],cap);
  }
  a.box(tower,[w+.28,.16,w+.28],[0,h+.42,0],cap);
  for(const side of [-1,1]){
   a.box(tower,[w+.16,.35,.15],[0,h+.65,side*(w/2+.04)],stone);
   a.box(tower,[.15,.35,w+.16],[side*(w/2+.04),h+.65,0],stone);
   for(const x of [-.62,-.21,.21,.62]){
    a.box(tower,[.27,.32,.23],[x,h+.97,side*(w/2+.04)],cap);
    a.box(tower,[.23,.32,.27],[side*(w/2+.04),h+.97,x],cap);
   }
  }
  // Dark recessed doorway with stone jambs, instead of a solid painted door.
  a.box(tower,[.55,1.02,.03],[0,.87,w/2+.02],a.materials.dark);
  for(const x of [-.35,.35])a.box(tower,[.13,1.1,.12],[x,.91,w/2+.07],cap);
  a.box(tower,[.83,.15,.15],[0,1.49,w/2+.07],cap);
  const flag=banner(a,tower,0,h+.50,0,j*1.7);flag.scale.setScalar(.65+.35*(1+Math.cos(q))/2);
  // A small beacon turns within a fixed protective brazier.
  const flame=new T.Group();flame.position.set(.45,h+.55,.25);tower.add(flame);
  a.cylinder(flame,.13,.12,[0,.08,0],a.materials.dark);
  const fire=a.mesh(flame,new T.ConeGeometry(.15,.48,5),new T.MeshStandardMaterial({color:0xffb447,emissive:0xff8d22,emissiveIntensity:1.2}),[0,.33,0]);fire.visible=false;a.wallBeacons.push({fire});
  jointMotion(a,flame,{axis:'z',speed:2.2,amplitude:.10,phase:j});
 }
 return wall;
}
