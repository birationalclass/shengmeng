import * as T from '../3d/vendor/three.module.js';
import {smooth,clamp,mix,cameraAt} from './story.mjs?v=20260920b';
const TAU=Math.PI*2;
function rng(seed=818){return()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};}
const rand=rng();
const v=(x,y,z)=>new T.Vector3(x,y,z);
const color={gold:0xc7a261,brass:0x9d763d,dark:0x27372f,wood:0x493a29,ivory:0xe0d1ab,teal:0x64b9b2};
const cache=new Map();
function geo(key,fn){if(!cache.has(key))cache.set(key,fn());return cache.get(key);}
function texture(canvas){const t=new T.CanvasTexture(canvas);t.colorSpace=T.SRGBColorSpace;t.anisotropy=4;return t;}
function canvas(w,h){const c=document.createElement('canvas');c.width=w;c.height=h;return [c,c.getContext('2d')];}
function woodTexture(){const [c,x]=canvas(512,512);x.fillStyle='#5b4630';x.fillRect(0,0,512,512);const r=rng(54);for(let i=0;i<1200;i++){const y=r()*512;x.strokeStyle=`rgba(${r()>.4?'22,18,9':'218,176,109'},${.02+r()*.13})`;x.lineWidth=.3+r()*1.5;x.beginPath();for(let k=0;k<=512;k+=8){const yy=y+3*Math.sin(k*.026+y)+1.4*Math.cos(k*.053+y*2);k?x.lineTo(k,yy):x.moveTo(k,yy);}x.stroke();}const t=texture(c);t.wrapS=t.wrapT=T.RepeatWrapping;return t;}
function mapTexture(){const [c,x]=canvas(2048,1024);x.fillStyle='#233229';x.fillRect(0,0,c.width,c.height);const r=rng(71);for(let i=0;i<48000;i++){x.fillStyle=`rgba(213,192,142,${r()*.04})`;x.fillRect(r()*2048,r()*1024,1+r()*2,1);}
 x.strokeStyle='#b9a37024';x.lineWidth=.7;for(let y=30;y<1024;y+=24){x.beginPath();for(let k=0;k<2048;k+=6){const yy=y+30*Math.sin(k*.008+y*.017)+12*Math.sin(k*.023+y*.02);k?x.lineTo(k,yy):x.moveTo(k,yy);}x.stroke();}
 x.strokeStyle='#d4b88535';for(let k=0;k<2048;k+=128){x.beginPath();x.moveTo(k,0);x.lineTo(k,1024);x.stroke();}for(let k=0;k<1024;k+=128){x.beginPath();x.moveTo(0,k);x.lineTo(2048,k);x.stroke();}
 x.font='16px Atlas,serif';x.fillStyle='#d3bd8d88';x.textAlign='center';for(let i=0;i<15;i++)x.fillText(String(i*15)+'°',i*128+128,34);
 for(const [cx,cy] of [[380,780],[1570,230]]){for(const radius of [50,63,80]){x.beginPath();x.arc(cx,cy,radius,0,TAU);x.stroke();}for(let i=0;i<16;i++){const a=i*TAU/16;x.beginPath();x.moveTo(cx+Math.sin(a)*20,cy+Math.cos(a)*20);x.lineTo(cx+Math.sin(a)*80,cy+Math.cos(a)*80);x.stroke();}x.fillText('N',cx,cy-95);}
 return texture(c);
}
function labelTexture(text,{size=90,sub='',bg='#25382d',ink='#dfc58c',width=1024,height=256}={}){const [c,x]=canvas(width,height);x.fillStyle=bg;x.fillRect(0,0,width,height);x.strokeStyle='#cda96155';x.lineWidth=3;x.strokeRect(12,12,width-24,height-24);x.fillStyle=ink;x.textAlign='center';x.textBaseline='middle';x.font=`${size}px Atlas,'Songti SC',serif`;x.fillText(text,width/2,sub?height*.4:height*.51,width*.89);if(sub){x.font=`${Math.round(size*.28)}px Inter,sans-serif`;x.fillStyle='#c9b995';x.fillText(sub,width/2,height*.77,width*.9);}return texture(c);}
export class AtlasScene{
 constructor(canvas,quality='standard'){
  this.canvas=canvas;this.renderer=new T.WebGLRenderer({canvas,antialias:true,alpha:false,powerPreference:'high-performance'});this.renderer.setClearColor(0x0a1511);this.renderer.outputColorSpace=T.SRGBColorSpace;this.renderer.toneMapping=T.ACESFilmicToneMapping;this.renderer.toneMappingExposure=1.22;this.renderer.shadowMap.enabled=true;this.renderer.shadowMap.type=T.PCFSoftShadowMap;
  this.scene=new T.Scene();this.scene.background=new T.Color(0x0d1914);this.scene.fog=new T.FogExp2(0x0d1914,.011);this.camera=new T.PerspectiveCamera(38,1,.1,230);this.rotating=[];this.risers=[];this.manual=null;
  this.materials={gold:new T.MeshStandardMaterial({color:color.gold,metalness:.72,roughness:.3}),brass:new T.MeshStandardMaterial({color:color.brass,metalness:.75,roughness:.4}),dark:new T.MeshStandardMaterial({color:color.dark,metalness:.5,roughness:.52}),wood:new T.MeshStandardMaterial({map:woodTexture(),color:0xc8a36d,roughness:.65,metalness:.08}),stone:new T.MeshStandardMaterial({color:0x898574,roughness:.88}),paper:new T.MeshStandardMaterial({color:color.ivory,roughness:.77}),jade:new T.MeshStandardMaterial({color:0x507660,roughness:.57,metalness:.36}),red:new T.MeshStandardMaterial({color:0x9e3922,roughness:.29,metalness:.2}),glow:new T.MeshStandardMaterial({color:0x91d2c6,emissive:0x529d91,emissiveIntensity:1.2,metalness:.38,roughness:.26})};
  const env=new T.Scene();env.background=new T.Color(0x4a5549);for(const [p,s,c]of [[[0,14,0],[20,1,18],0xe3d2a7],[[-12,3,8],[1,10,18],0x93b3b0],[[10,5,-8],[1,12,12],0xffffff]]){const m=new T.Mesh(new T.BoxGeometry(...s),new T.MeshBasicMaterial({color:c}));m.position.set(...p);env.add(m);}const pm=new T.PMREMGenerator(this.renderer);this.environment=pm.fromScene(env,.02);this.scene.environment=this.environment.texture;pm.dispose();env.traverse(o=>{o.geometry?.dispose();o.material?.dispose();});
  this.scene.add(new T.HemisphereLight(0xfce8bb,0x152b27,2.0));const key=new T.DirectionalLight(0xffe0a0,4.2);key.position.set(-13,26,18);key.castShadow=true;key.shadow.mapSize.set(1536,1536);Object.assign(key.shadow.camera,{left:-48,right:48,top:25,bottom:-25,near:1,far:95});key.shadow.bias=-.0005;key.shadow.normalBias=.045;this.scene.add(key);this.key=key;const fill=new T.DirectionalLight(0x83bcc4,2.3);fill.position.set(6,11,-22);this.scene.add(fill);const rim=new T.DirectionalLight(0xfff0d1,1.5);rim.position.set(25,13,5);this.scene.add(rim);
  const table=this.box(this.scene,[80,.8,40],[0,-1.4,0],this.materials.wood);table.receiveShadow=true;this.box(this.scene,[80.5,.12,40.5],[0,-1.05,0],this.materials.brass);
  const map=new T.Mesh(new T.PlaneGeometry(80,40),new T.MeshStandardMaterial({map:mapTexture(),roughness:.91,metalness:.05}));map.rotation.x=-Math.PI/2;map.position.y=-.97;map.receiveShadow=true;this.scene.add(map);
  this.platforms=[-22,0,22].map((x,i)=>this.platform(x,i));
  this.makeWriting(this.platforms[0]);this.makeNewton(this.platforms[1]);this.makeAI(this.platforms[2]);this.makeConnections();this.makeDust();this.makeOrrery();this.setQuality(quality);this.resize();
 }
 mesh(parent,geometry,material,pos=[0,0,0]){const m=new T.Mesh(geometry,material);m.position.set(...pos);m.castShadow=true;m.receiveShadow=true;parent.add(m);return m;}
 box(parent,size,pos,mat=this.materials.brass){const m=this.mesh(parent,geo('box',()=>new T.BoxGeometry(1,1,1)),mat,pos);m.scale.set(...size);return m;}
 cylinder(parent,r,h,pos,mat=this.materials.brass,r2=r){return this.mesh(parent,geo(`c${r},${r2},${h}`,()=>new T.CylinderGeometry(r,r2,h,48)),mat,pos);}
 torus(parent,r,t,pos,mat=this.materials.gold,rotation=[Math.PI/2,0,0]){const m=this.mesh(parent,geo(`t${r},${t}`,()=>new T.TorusGeometry(r,t,8,96)),mat,pos);m.rotation.set(...rotation);return m;}
 line(parent,points,col=0xc3a875,opacity=.55){const g=new T.BufferGeometry().setFromPoints(points.map(p=>Array.isArray(p)?v(...p):p));const l=new T.Line(g,new T.LineBasicMaterial({color:col,transparent:true,opacity}));parent.add(l);return l;}
 rod(parent,a,b,r=.07,mat=this.materials.gold){const start=v(...a),end=v(...b),d=end.clone().sub(start),m=this.cylinder(parent,r,d.length(),[0,0,0],mat);m.position.copy(start.add(end).multiplyScalar(.5));m.quaternion.setFromUnitVectors(v(0,1,0),d.normalize());return m;}
 plate(parent,text,pos,w=4,h=1,opts={}){const m=this.mesh(parent,new T.PlaneGeometry(w,h),new T.MeshStandardMaterial({map:labelTexture(text,opts),roughness:.63,metalness:.23,transparent:false}),pos);m.rotation.x=-Math.PI/2;return m;}
 gear(parent,r,teeth,pos,speed=.07,mat=this.materials.brass){
  const g=geo(`gear${r}-${teeth}`,()=>{const s=new T.Shape();for(let i=0;i<teeth*4;i++){const a=i*TAU/(teeth*4),rr=r*(i%4===1||i%4===2?1:.87),x=Math.cos(a)*rr,y=Math.sin(a)*rr;i?s.lineTo(x,y):s.moveTo(x,y);}s.closePath();const hole=new T.Path();hole.absarc(0,0,r*.37,0,TAU,true);s.holes.push(hole);return new T.ExtrudeGeometry(s,{depth:.18,bevelEnabled:true,bevelThickness:.025,bevelSize:.025,bevelSegments:1,steps:1});});
  const group=new T.Group();parent.add(group);group.position.set(...pos);const wheel=this.mesh(group,g,mat);wheel.rotation.x=-Math.PI/2;for(let i=0;i<6;i++){const spoke=this.box(group,[r*.72,.16,.10],[Math.cos(i*TAU/6)*r*.53,.09,Math.sin(i*TAU/6)*r*.53],mat);spoke.rotation.y=-i*TAU/6;}this.cylinder(group,r*.16,.28,[0,.06,0],this.materials.gold);this.rotating.push({object:group,speed});return group;
 }
 platform(x,i){const p=new T.Group();p.position.x=x;this.scene.add(p);this.cylinder(p,7.65,.6,[0,-.55,0],this.materials.dark);this.cylinder(p,7.38,.23,[0,-.16,0],this.materials.brass);this.cylinder(p,7.08,.27,[0,.04,0],this.materials.wood);this.torus(p,7.22,.08,[0,.15,0]);this.torus(p,6.78,.035,[0,.20,0]);
  const ticks=new T.InstancedMesh(geo('tick',()=>new T.BoxGeometry(.035,.04,.22)),this.materials.gold,120),o=new T.Object3D();for(let k=0;k<120;k++){const a=k*TAU/120;o.position.set(Math.sin(a)*7,.22,Math.cos(a)*7);o.rotation.y=a;o.scale.set(1,1,k%5===0?1.8:1);o.updateMatrix();ticks.setMatrixAt(k,o.matrix);}p.add(ticks);
  for(let j=0;j<3;j++)this.gear(p,1.0+j*.23,16+j*4,[-4+j*4,-.37,5.65],(j%2?-1:1)*(.12+j*.015));
  this.plate(p,['I · THE WRITTEN WORLD','II · THE MOVING WORLD','III · THE GENERATED WORLD'][i],[0,.222,5],8.2,.68,{size:51,width:1024,height:128});
  for(let j=0;j<10;j++){const a=j*TAU/10;this.cylinder(p,.07,.07,[Math.sin(a)*7.28,.21,Math.cos(a)*7.28],this.materials.gold);}
  return p;
 }
 makeWriting(p){
  const g=new T.Group();p.add(g);this.writing=g;this.risers.push({object:g,start:7,end:15});
  this.box(g,[10,.45,6.6],[0,.52,-.3],this.materials.dark);this.box(g,[9.65,.13,6.25],[0,.82,-.3],this.materials.wood);
  const letters=['山','川','日','月','W','O','R','D'];this.letters=[];
  letters.forEach((c,i)=>{const x=(i%4-1.5)*1.62,z=i<4?-1.65:.7,tile=new T.Group();tile.position.set(x,1,z);g.add(tile);this.box(tile,[1.34,.38,1.45],[0,0,0],this.materials.brass);this.box(tile,[1.22,.07,1.34],[0,.23,0],this.materials.dark);this.plate(tile,c,[0,.273,0],1.13,1.23,{size:148,width:256,height:256,ink:'#ead8a7'});for(const s of [-1,1])this.cylinder(g,.095,.9,[x+s*.45,.9,z],this.materials.gold);this.letters.push({object:tile,x,z,i});});
  this.plate(g,'山 川 · WORD',[0,.91,2.16],7.2,.57,{size:66,width:1024,height:128});
  this.gear(g,1.3,22,[-5.2,1,-.5],.21);this.gear(g,.88,16,[-5.3,1.03,1.65],-.31);this.gear(g,1,18,[5.1,1,-1.8],-.22);
  for(const x of [-4.4,4.4]){this.cylinder(g,.17,3.15,[x,2.05,-2.85],this.materials.brass);this.cylinder(g,.28,.16,[x,3.66,-2.85],this.materials.gold);}this.rod(g,[-4.4,3.65,-2.85],[4.4,3.65,-2.85],.11,this.materials.brass);
  const page=this.plate(g,'Σ⁺',[0,2.45,-2.82],2.5,1.25,{size:133,width:512,height:256,sub:'THE ART OF CONCATENATION'});page.rotation.x=0;
  for(let j=0;j<18;j++){const x=-3.7+(j%9)*.92,z=-4.45+Math.floor(j/9)*.66;this.box(g,[.75,.13,.5],[x,.39,z],this.materials.dark);this.plate(g,String.fromCharCode(65+j),[x,.46,z],.52,.4,{size:90,width:128,height:128});}
  const book=new T.Group();g.add(book);book.position.set(4.55,1.1,2.8);book.rotation.y=-.28;for(const sign of [-1,1]){const half=this.box(book,[1.0,.15,1.55],[sign*.5,.1,0],this.materials.paper);half.rotation.z=-sign*.13;for(let j=0;j<7;j++)this.rod(book,[sign*.14,.22,-.52+j*.16],[sign*.88,.22,-.52+j*.16],.008,this.materials.brass);}
 }
 makeNewton(p){
  const g=new T.Group();p.add(g);this.tree=g;this.risers.push({object:g,start:36,end:44});this.gear(g,3.2,44,[0,.27,0],.05,this.materials.dark);this.cylinder(g,2.8,.22,[0,.48,0],this.materials.brass);this.cylinder(g,2.7,.24,[0,.68,0],this.materials.wood);
  const tips=[];const r=rng(1234);const branch=(a,b,thickness,depth)=>{const mid=a.clone().lerp(b,.5);mid.x+=(r()-.5)*.6;mid.z+=(r()-.5)*.6;const curve=new T.CatmullRomCurve3([a,mid,b]);this.mesh(g,new T.TubeGeometry(curve,8,thickness,7,false),depth>1?this.materials.wood:this.materials.brass);
   if(depth===0){tips.push(b);return;}const n=depth===3?4:3;for(let j=0;j<n;j++){const angle=j*TAU/n+r()*1.9,len=1.1+depth*.47,end=b.clone().add(v(Math.cos(angle)*len*.73,.65+r()*1.0,Math.sin(angle)*len*.73));branch(b,end,thickness*.58,depth-1);}};
  branch(v(0,.8,0),v(.15,3.7,0),.46,3);
  const leafG=geo('leaf',()=>new T.IcosahedronGeometry(.22,1)),leaves=new T.InstancedMesh(leafG,this.materials.jade,tips.length*9),o=new T.Object3D();let count=0;
  for(const tip of tips)for(let j=0;j<9;j++){o.position.copy(tip).add(v((r()-.5)*1.35,(r()-.5)*.7,(r()-.5)*1.35));o.rotation.set(r()*Math.PI,r()*TAU,r()*Math.PI);o.scale.set(1.9+r(),.28,.8+r());o.updateMatrix();leaves.setMatrixAt(count,o.matrix);leaves.setColorAt(count,new T.Color().setHSL(.11+r()*.11,.2+r()*.15,.25+r()*.18));count++;}leaves.castShadow=true;g.add(leaves);
  const appleGeometry=new T.SphereGeometry(.31,24,18);const pos=appleGeometry.attributes.position;for(let i=0;i<pos.count;i++){const x=pos.getX(i),y=pos.getY(i),z=pos.getZ(i),theta=Math.atan2(z,x),bulge=1+.05*Math.cos(theta*5);pos.setXYZ(i,x*bulge,y*(.9+.06*Math.cos(theta*5)),z*bulge);}appleGeometry.computeVertexNormals();
  this.apples=[];for(let j=0;j<9;j++){const tip=tips[Math.floor(j*tips.length/9)],a=new T.Group();a.position.copy(tip).add(v(0,-.52,0));this.mesh(a,appleGeometry,this.materials.red);this.rod(a,[0,.24,0],[.025,.45,0],.035,this.materials.wood);g.add(a);this.apples.push(a);}this.fallingApple=this.apples[4];this.appleOrigin=this.fallingApple.position.clone();
  this.torus(g,3.85,.04,[0,1.1,0],this.materials.gold,[.25,0,0]);const orbit=new T.Group();g.add(orbit);orbit.position.set(0,2.1,0);this.torus(orbit,4.6,.035,[0,0,0],this.materials.gold,[.6,.35,.1]);this.rotating.push({object:orbit,speed:.028});this.orbit=orbit;
  // A seated, deliberately sculptural Newton figure; the apple never hits him.
  const man=new T.Group();g.add(man);man.position.set(-3.1,.85,2.2);man.rotation.y=.3;this.box(man,[1.45,.17,.55],[0,.4,0],this.materials.wood);for(const x of [-.55,.55])this.box(man,[.1,.6,.45],[x,.04,0],this.materials.brass);const coat=this.mesh(man,new T.ConeGeometry(.36,1.25,12),this.materials.dark,[0,1.07,0]);coat.rotation.x=-.15;this.mesh(man,geo('head',()=>new T.SphereGeometry(.25,16,12)),this.materials.paper,[0,1.85,.03]);for(const x of [-.17,.17]){this.rod(man,[x,.74,.02],[x,.48,.65],.115,this.materials.dark);this.rod(man,[x,.48,.65],[x,-.15,.7],.08,this.materials.dark);}this.box(man,[.55,.06,.47],[.05,.96,.61],this.materials.paper);
  // Ivory curls, coat sleeves and a writing hand identify the miniature scholar.
  for(const side of [-1,1]){this.rod(man,[side*.27,1.47,.04],[side*.43,1.13,.30],.10,this.materials.dark);this.rod(man,[side*.43,1.13,.30],[side*.19,1.03,.61],.075,this.materials.dark);this.mesh(man,new T.SphereGeometry(.085,10,8),this.materials.paper,[side*.19,1.03,.61]);for(let j=0;j<4;j++){const curl=this.mesh(man,new T.SphereGeometry(.12,10,8),this.materials.paper,[side*.22,1.98-j*.115,-.1]);curl.scale.set(.8,1.2,1.0);}}for(let j=0;j<3;j++)this.mesh(man,new T.SphereGeometry(.025,8,6),this.materials.gold,[0,1.34-j*.15,.2]);
  const house=new T.Group();g.add(house);house.position.set(3.8,.25,-3.3);this.box(house,[2.0,1.5,1.45],[0,.75,0],this.materials.stone);const roof=this.mesh(house,new T.ConeGeometry(1.7,1.1,4),this.materials.dark,[0,2.0,0]);roof.rotation.y=Math.PI/4;roof.scale.z=.8;for(const x of [-.62,0,.62])for(const y of [.5,1.1])this.box(house,[.22,.32,.035],[x,y,.745],this.materials.gold);this.box(house,[.22,.85,.25],[.7,2.12,-.25],this.materials.stone);
  this.plate(g,'PHILOSOPHIÆ NATURALIS',[0,.30,3.72],5.8,.48,{size:49,width:1024,height:128});
 }
 makeAI(p){
  const g=new T.Group();p.add(g);this.ai=g;this.risers.push({object:g,start:68,end:77});this.cylinder(g,3.5,.3,[0,.5,0],this.materials.dark);this.torus(g,3.45,.055,[0,.67,0]);
  const layers=[5,7,7,5],nodes=[],all=[];for(let l=0;l<4;l++){const x=-3.75+l*2.5;const layer=[];this.box(g,[.7,.12,5.3],[x,.47,0],this.materials.brass);for(let j=0;j<layers[l];j++){const angle=j*TAU/layers[l]+.3*l,pt=v(x,3.8+Math.sin(angle)*2.1,Math.cos(angle)*2.1);layer.push(pt);all.push({pt,l,j});}nodes.push(layer);const arch=this.torus(g,2.75,.055,[x,3.8,0],this.materials.gold,[0,Math.PI/2,0]);for(const z of [-2,2])this.rod(g,[x,.6,z],[x,3.8,z*1.37],.065,this.materials.brass);}
  const nodeGeometry=geo('node',()=>new T.IcosahedronGeometry(.19,1));this.neurons=all.map(({pt,l,j})=>({mesh:this.mesh(g,nodeGeometry,this.materials.glow,pt.toArray()),l,j}));
  const segments=[];this.synapses=[];for(let l=0;l<3;l++)for(let i=0;i<nodes[l].length;i++)for(let j=0;j<nodes[l+1].length;j++){const a=nodes[l][i],b=nodes[l+1][j];segments.push(...a.toArray(),...b.toArray());this.synapses.push({a,b,l,offset:(i*3+j)*.079});}
  const geoLines=new T.BufferGeometry();geoLines.setAttribute('position',new T.Float32BufferAttribute(segments,3));this.neuralLines=new T.LineSegments(geoLines,new T.LineBasicMaterial({color:0xc9af76,transparent:true,opacity:.20}));g.add(this.neuralLines);
  this.pulses=new T.InstancedMesh(geo('pulse',()=>new T.SphereGeometry(.047,6,4)),new T.MeshBasicMaterial({color:0x9cfff0}),this.synapses.length);g.add(this.pulses);
  for(let j=0;j<12;j++){const a=j*TAU/12;const server=this.box(g,[.45,.7+rand()*.9,.55],[Math.sin(a)*5.35,.8,Math.cos(a)*5.35],this.materials.dark);for(let k=0;k<4;k++)this.box(server,[.64,.025,.07],[0,-.25+k*.14,.51],this.materials.gold);}
  this.gear(g,1.45,24,[-4.8,.56,3.1],.13);this.gear(g,1.45,24,[4.8,.56,-3.1],-.13);
  const core=new T.Group();g.add(core);core.position.set(0,4,0);for(let j=0;j<3;j++)this.torus(core,1.1+j*.3,.025,[0,0,0],this.materials.gold,[j*.8,j*.6,j*.4]);this.rotating.push({object:core,speed:.18});
  this.plate(g,'INPUT  →  TRANSFORM  →  GENERATE',[0,.75,3.95],7.3,.62,{size:42,width:1024,height:128});
 }
 makeConnections(){for(const mid of [-11,11]){const group=new T.Group();this.scene.add(group);for(let i=0;i<3;i++)this.gear(group,1.18,20,[mid+(i-1)*2.12,-.64,1.8],i%2?-.16:.16);for(const z of [-.8,-1.4])this.rod(this.scene,[mid-4,-.53,z],[mid+4,-.53,z],.045,this.materials.brass);for(let i=0;i<24;i++)this.box(this.scene,[.14,.12,.42],[mid-4+i*.35,-.62,-1.1],this.materials.gold);}}
 makeDust(){const r=rng(99),a=[];for(let i=0;i<650;i++)a.push((r()-.5)*90,r()*18,(r()-.5)*45);const g=new T.BufferGeometry();g.setAttribute('position',new T.Float32BufferAttribute(a,3));const [c,x]=canvas(32,32),gradient=x.createRadialGradient(16,16,0,16,16,16);gradient.addColorStop(0,'#ffffee');gradient.addColorStop(.15,'#fff1ce');gradient.addColorStop(1,'#fff0');x.fillStyle=gradient;x.fillRect(0,0,32,32);this.dust=new T.Points(g,new T.PointsMaterial({color:0xf3d5a0,size:.11,map:texture(c),transparent:true,opacity:.45,depthWrite:false,blending:T.AdditiveBlending}));this.scene.add(this.dust);}
 makeOrrery(){const group=new T.Group();group.position.set(0,12,-11);this.scene.add(group);for(let i=0;i<3;i++){const ring=new T.Group();group.add(ring);ring.rotation.set(.2+i*.7,.3+i*.6,0);this.torus(ring,2.2+i*.32,.08,[0,0,0],this.materials.brass,[0,0,0]);this.rotating.push({object:ring,speed:(i%2?-.07:.09)});}this.mesh(group,new T.SphereGeometry(.9,32,20),new T.MeshStandardMaterial({color:0xcda86a,emissive:0xaa722a,emissiveIntensity:.5,metalness:.6,roughness:.35}));this.orrery=group;}
 setQuality(q){this.quality=q;this.renderer.setPixelRatio(Math.min(devicePixelRatio||1,q==='high'?2:q==='low'?1:1.5));this.renderer.shadowMap.enabled=q!=='low';this.resize();}
 resize(){const w=this.canvas.clientWidth||innerWidth,h=this.canvas.clientHeight||innerHeight;this.renderer.setSize(w,h,false);this.camera.aspect=w/h;this.camera.setViewOffset(w,h,w<600?0:-w*.13,w<600?-h*.15:0,w,h);this.camera.updateProjectionMatrix();}
 takeControl(){const target=this.currentTarget||v(0,2,0),offset=this.camera.position.clone().sub(target);this.manual={target:target.clone(),radius:offset.length(),theta:Math.atan2(offset.x,offset.z),phi:Math.acos(clamp(offset.y/offset.length(),-1,1))};}
 orbit(dx,dy){if(!this.manual)this.takeControl();this.manual.theta-=dx*.006;this.manual.phi=clamp(this.manual.phi+dy*.004,.23,1.45);}
 zoom(delta){if(!this.manual)this.takeControl();this.manual.radius=clamp(this.manual.radius*Math.exp(delta*.001),10,88);}
 update(t){
  for(const {object,speed}of this.rotating)object.rotation.y=t*speed;
  for(const {object,start,end}of this.risers){const amount=smooth((t-start)/(end-start));object.scale.y=Math.max(.008,amount);object.visible=amount>.002;}
  const join=smooth((t-24)/5);for(const {object,x,z,i}of this.letters){object.position.x=x*(i>=4?mix(1,.86,join):1);object.position.y=1+.14*Math.sin(t*.7+i)*smooth((t-9-i*.45)/3);object.position.z=z;}
  const drop=clamp((t-51)/4),ay=Math.max(.96,this.appleOrigin.y-(this.appleOrigin.y-.96)*drop*drop);this.fallingApple.position.set(this.appleOrigin.x,ay,this.appleOrigin.z);this.fallingApple.rotation.z=drop*.6;
  const o=new T.Object3D();this.synapses.forEach(({a,b,l,offset},i)=>{const progress=((t*.32-l*.27-offset)%1+1)%1;o.position.copy(a).lerp(b,progress);o.scale.setScalar(smooth((t-77)/4)*(.55+.45*Math.sin(Math.PI*progress)));o.updateMatrix();this.pulses.setMatrixAt(i,o.matrix);});this.pulses.instanceMatrix.needsUpdate=true;
  this.neurons.forEach(({mesh,l,j})=>mesh.scale.setScalar(1+.17*Math.sin(t*2.0-l*1.0+j*.5)));this.dust.rotation.y=t*.002;this.dust.position.y=Math.sin(t*.1)*.4;
  const {pos,target}=cameraAt(t,this.camera.aspect);this.currentTarget=v(...target);
  if(this.manual){const {target:aim,radius,theta,phi}=this.manual;this.camera.position.set(aim.x+radius*Math.sin(phi)*Math.sin(theta),aim.y+radius*Math.cos(phi),aim.z+radius*Math.sin(phi)*Math.cos(theta));this.camera.lookAt(aim);}else{this.camera.position.set(...pos);this.camera.lookAt(this.currentTarget);}
  this.renderer.render(this.scene,this.camera);
 }
}
