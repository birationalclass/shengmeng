import * as T from '../3d/vendor/three.module.js';
import {installBoards,paintBoard,cellPoint} from './board-world.mjs?v=world2';
import {illustratedMap} from './map-texture.mjs?v=world2';
import {AtlasScene} from '../test-module/scene.mjs?v=20260920gears1';
export const REGIONS=[
 {n:2,en:'THE FIRST GATE',zh:'初始之门',group:'C₂'},
 {n:3,en:'THE JADE COURT',zh:'玉阶庭院',group:'C₃'},
 {n:4,en:'THE FOURFOLD GARDEN',zh:'四元花园',group:'C₂ × C₂'},
 {n:5,en:'THE IVORY ABBEY',zh:'象牙修道院',group:'C₅'},
 {n:6,en:'THE PERMUTATION HALL',zh:'置换殿堂',group:'S₃'},
 {n:7,en:'THE SEVENTH SPIRE',zh:'第七尖塔',group:'C₇'},
 {n:8,en:'THE MIRROR CITADEL',zh:'镜像城塞',group:'D₄'},
 {n:9,en:'THE NINEFOLD ARCHIVE',zh:'九宫藏馆',group:'C₃ × C₃'}
];
export const PLACES=[[-39,18],[-13,18],[13,18],[39,18],[39,-18],[13,-18],[-13,-18],[-39,-18]];
const V=(...a)=>new T.Vector3(...a);
function parchment(){
 const c=document.createElement('canvas');c.width=2048;c.height=1280;const x=c.getContext('2d');
 const gr=x.createRadialGradient(970,610,80,1024,640,1200);gr.addColorStop(0,'#d8c799');gr.addColorStop(.8,'#b79b69');gr.addColorStop(1,'#876a43');x.fillStyle=gr;x.fillRect(0,0,2048,1280);
 let seed=7841;const r=()=>((seed=(Math.imul(seed,1664525)+1013904223)>>>0)/4294967296);
 for(let i=0;i<65000;i++){x.fillStyle=r()>.5?'#fff5d00c':'#442b1b0b';x.fillRect(r()*2048,r()*1280,1+r()*3,1+r()*2);}
 x.lineWidth=1;for(let y=40;y<1280;y+=22){x.strokeStyle='#66522d22';x.beginPath();for(let j=0;j<=2048;j+=8){const z=y+15*Math.sin(j*.018+y*.032)+8*Math.cos(j*.033-y*.026);j?x.lineTo(j,z):x.moveTo(j,z);}x.stroke();}
 for(let inset of [30,42,65]){x.strokeStyle='#61472077';x.lineWidth=inset===42?2:1;x.strokeRect(inset,inset,2048-inset*2,1280-inset*2);}
 x.save();x.translate(1024,640);for(let i=0;i<16;i++){x.rotate(Math.PI/8);x.strokeStyle='#614b3377';x.lineWidth=i%4===0?3:1;x.beginPath();x.moveTo(0,-30);x.lineTo(0,-110);x.stroke();}for(let radius of [38,97,113]){x.beginPath();x.arc(0,0,radius,0,Math.PI*2);x.stroke();}x.fillStyle='#574225';x.font='28px Georgia';x.textAlign='center';x.fillText('N',0,-127);x.restore();
 x.textAlign='center';x.fillStyle='#5d472e';x.font='30px Georgia';x.fillText('TERRA · ALGEBRA',1024,1160);x.font='15px Georgia';x.fillText('EIGHT DOMAINS OF COMPOSITION',1024,1193);
 const tex=new T.CanvasTexture(c);tex.colorSpace=T.SRGBColorSpace;return tex;
}
export class SudokuAtlas extends AtlasScene{
 constructor(canvas){
  super(canvas,'standard');this.scene.background.setHex(0xa58c63);this.scene.fog.color.setHex(0xa58c63);this.scene.fog.density=.0015;this.renderer.toneMappingExposure=1.1;
  this.markers=[];for(let i=0;i<8;i++){const ring=this.torus(this.platforms[i],7.52,.10,[0,.30,0],new T.MeshStandardMaterial({color:0xc49a4c,emissive:0x77511b,emissiveIntensity:.25,metalness:.7,roughness:.35}));this.markers.push(ring);}
  for(const {object}of this.risers){object.position.y=0;object.visible=true;}this.animateNewScenes(205);for(const {g}of this.architecture){g.position.y=0;g.visible=true;}
  this.fromPos=V(3,110,115);this.toPos=this.fromPos.clone();this.camera.position.copy(this.fromPos);this.fromAim=V(0,0,0);this.toAim=this.fromAim.clone();this.currentTarget=this.fromAim.clone();this.flight=1;this.selected=-1;this.orrery.visible=false;
  installBoards(this);delete this.orbit;
  this.ray=new T.Raycaster();this.hitMeshes=this.boards.map(b=>b.mesh);
 }
 makeTerrain(){
  const board=this.box(this.scene,[124,1.8,88],[0,-2,0],this.materials.wood);board.receiveShadow=true;
  this.box(this.scene,[123,.18,87],[0,-1.02,0],this.materials.brass);
  const plane=new T.Mesh(new T.PlaneGeometry(122,86),new T.MeshStandardMaterial({map:parchment(),roughness:.95}));plane.rotation.x=-Math.PI/2;plane.position.y=-.91;plane.receiveShadow=true;this.scene.add(plane);this.terrainPlane=plane;this.mechanicalTexture=plane.material.map;this.parchmentTexture=illustratedMap();plane.material.map=this.parchmentTexture;
  for(let k=0;k<32;k++){const x=-56+k*3.5,z=-34+Math.sin(k*.63)*2;const h=.5+(k%4)*.4;const m=this.mesh(this.scene,new T.ConeGeometry(.5+(k%3)*.25,h,5),this.materials.stone,[x,-.8+h/2,z]);m.rotation.y=k*.8;}
  for(let k=0;k<5;k++)this.torus(this.scene,2+k*.45,.025,[0,-.82,0],this.materials.brass);
 }
 makeNameplate(p,i){
  const info=REGIONS[i];const plaque=new T.Group();p.add(plaque);plaque.position.set(0,-.24,9.2);
  this.box(plaque,[10.3,.32,2.25],[0,0,0],this.materials.brass);this.box(plaque,[10.0,.10,2.0],[0,.19,0],this.materials.dark);
  this.plate(plaque,`${info.n} × ${info.n}  /  ${info.zh}`,[0,.26,0],9.8,1.85,{size:72,sub:info.en,bg:'#c8b185',ink:'#392b1e',width:1536,height:320});
  for(const x of [-4.85,4.85])for(const z of [-.85,.85])this.cylinder(plaque,.065,.07,[x,.26,z],this.materials.gold);
 }
 makeConnections(){
  this.platforms.push(this.platform(0,6),this.platform(0,7));
  this.platforms.forEach((p,i)=>p.position.set(PLACES[i][0],0,PLACES[i][1]));
  this.buildCitadel(this.platforms[6]);this.buildArchive(this.platforms[7]);this.bridges=[];
  for(let i=0;i<7;i++){
   const a=this.platforms[i].position,b=this.platforms[i+1].position,d=b.clone().sub(a),length=d.length()-21.4,g=new T.Group();g.position.copy(a.clone().add(b).multiplyScalar(.5));g.rotation.y=Math.atan2(d.x,d.z);this.scene.add(g);const leaves=[],chains=[];
   for(const sign of [-1,1]){
    this.box(g,[3,.3,3.6],[0,.01,sign*(length/2+1.8)],this.materials.stone);
    for(const x of [-1.4,1.4]){this.box(g,[.26,3.65,.28],[x,1.5,sign*length/2],this.materials.wood);this.cylinder(g,.2,.12,[x,3.4,sign*length/2]);}
    this.box(g,[3,.18,.3],[0,3.36,sign*length/2],this.materials.wood);
    const pivot=new T.Group();g.add(pivot);pivot.position.set(0,.25,sign*length/2);pivot.rotation.y=sign===1?Math.PI:0;leaves.push(pivot);const half=length/2;
    const count=Math.ceil(half/.32);for(let k=0;k<count;k++)this.box(pivot,[2.45,.13,.28],[0,0,(k+.5)*half/count],this.materials.wood);
    for(const x of [-1.08,1.08]){this.box(pivot,[.10,.14,half],[x,-.03,half/2],this.materials.brass);this.rod(pivot,[x,.72,0],[x,.72,half],.045);for(let k=0;k<5;k++)this.box(pivot,[.07,.7,.07],[x,.38,k*half/4],this.materials.wood);const geo=new T.BufferGeometry().setFromPoints([V(x,3.36,sign*length/2),V(x,.30,0)]);const line=new T.Line(geo,new T.LineBasicMaterial({color:0x493922}));g.add(line);chains.push({line,pivot,x,sign,half});}
    this.box(g,[1.7,.14,1.7],[-2.5,.08,sign*length/2],this.materials.dark);this.cylinder(g,.14,.3,[-2.5,.24,sign*length/2]);this.gear(g,.65,16,[-2.5,.46,sign*length/2],.12*sign);
   }
   for(const x of [-1.55,1.55]){const points=Array.from({length:21},(_,k)=>V(x,3.32-1.1*Math.sin(k*Math.PI/20),-length/2+k*length/20));this.mesh(g,new T.TubeGeometry(new T.CatmullRomCurve3(points),24,.04,5,false),this.materials.dark);}
   this.bridges.push({g,leaves,chains,length,start:0,end:1});
  }
 }
 buildCitadel(p){
  for(const x of [-3.4,3.4])for(const z of [-3.4,3.4]){const g=new T.Group();g.position.set(x,.25,z);p.add(g);this.cylinder(g,.85,4,[0,2,0],this.materials.stone);this.cylinder(g,1.03,.25,[0,4.1,0],this.materials.brass);for(let i=0;i<8;i++){const q=i*Math.PI/4;this.box(g,[.32,.55,.32],[Math.sin(q)*.8,4.5,Math.cos(q)*.8],this.materials.stone);}for(let y=1;y<4;y+=.9)this.box(g,[.22,.42,.06],[0,y,.855],this.materials.dark);}
  for(const z of [-3.4,3.4]){this.box(p,[5.2,2,.3],[0,1.25,z],this.materials.stone);for(let x=-2;x<=2;x+=.5)this.box(p,[.28,.35,.4],[x,2.43,z],this.materials.stone);}
  for(const x of [-3.4,3.4])this.box(p,[.3,2,5.2],[x,1.25,0],this.materials.stone);
  const dial=new T.Group();p.add(dial);dial.position.y=.4;for(let i=0;i<4;i++)this.torus(dial,1.2+i*.38,.07,[0,1+i*.15,0]);this.cylinder(dial,.2,2,[0,1,0]);this.rotating.push({object:dial,speed:.13});
 }
 buildArchive(p){
  this.box(p,[7.5,.35,6.6],[0,.4,0],this.materials.stone);
  for(const x of [-3,0,3])for(const z of [-2.5,0,2.5]){this.cylinder(p,.24,3.4,[x,2.25,z],this.materials.stone);this.cylinder(p,.4,.2,[x,.64,z]);this.cylinder(p,.42,.22,[x,4,z]);}
  this.box(p,[7.2,.28,6.4],[0,4.2,0],this.materials.wood);
  for(const sign of [-1,1]){const roof=this.box(p,[4.1,.16,7],[sign*1.75,5.05,0],this.materials.jade);roof.rotation.z=-sign*.42;for(let k=-12;k<=12;k++)this.rod(p,[0,5.82,k*.27],[sign*3.6,4.29,k*.27],.04,this.materials.brass);}
  for(let k=0;k<9;k++)this.box(p,[.8,.75,.8],[(k%3-1)*1.5,1.1,(Math.floor(k/3)-1)*1.5],this.materials.dark);
 }
 focus(index){
  this.manual=null;this.selected=index;this.fromPos=this.camera.position.clone();this.fromAim=this.currentTarget.clone();this.flight=0;
  if(index<0){this.toPos=V(3,100,108);this.toAim=V(0,0,0);}else{const [x,z]=PLACES[index];this.toPos=V(x,21,z+14);this.toAim=V(x,.4,z);}
  if(this.camera.aspect<.8&&index<0)this.toPos.multiplyScalar(1.55);
 }
 project(index){const [x,z]=PLACES[index];const p=V(x,1,z+8.5).project(this.camera);return {x:(p.x+1)*.5,y:(1-p.y)*.5,visible:p.z>-1&&p.z<1&&Math.abs(p.x)<1.1&&Math.abs(p.y)<1.1};}
 pick(x,y){this.ray.setFromCamera(new T.Vector2(x,y),this.camera);return this.ray.intersectObjects(this.hitMeshes)[0]?.object.userData.region??-1;}
 setProgress(done){this.markers.forEach((ring,i)=>{const cleared=done.includes(i+2);ring.material.color.setHex(cleared?0x699f80:0xc49a4c);ring.material.emissive.setHex(cleared?0x234b37:0x77511b);});}
 setMapStyle(style){this.terrainPlane.material.map=style==='mechanical'?this.mechanicalTexture:this.parchmentTexture;this.terrainPlane.material.needsUpdate=true;}
 paint(index,state){paintBoard(this,index,state);}
 cellProjection(index,k){const p=cellPoint(this,index,k).project(this.camera);return {x:(p.x+1)/2,y:(1-p.y)/2,visible:p.z>-1&&p.z<1&&Math.abs(p.x)<1&&Math.abs(p.y)<1};}
 zoom(delta){if(!this.manual)this.takeControl();this.manual.radius=Math.max(15,Math.min(230,this.manual.radius*Math.exp(delta*.001)));}
 updateWorld(t,dt,reduced=false){
  for(const {object,speed}of this.rotating)object.rotation.y=reduced?0:t*speed;
  this.dust.rotation.y=reduced?0:t*.002;
  if(this.manual){const {target:aim,radius,theta,phi}=this.manual;this.camera.position.set(aim.x+radius*Math.sin(phi)*Math.sin(theta),aim.y+radius*Math.cos(phi),aim.z+radius*Math.sin(phi)*Math.cos(theta));this.camera.lookAt(aim);this.currentTarget.copy(aim);}
  else{this.flight=Math.min(1,this.flight+dt/(reduced?.01:1.65));const u=this.flight*this.flight*(3-2*this.flight);this.camera.position.lerpVectors(this.fromPos,this.toPos,u);this.currentTarget.lerpVectors(this.fromAim,this.toAim,u);if(!reduced&&this.flight===1){this.camera.position.x+=Math.sin(t*.10)*.18;this.camera.position.y+=Math.cos(t*.12)*.10;}this.camera.lookAt(this.currentTarget);}
  this.renderer.render(this.scene,this.camera);
 }
}
