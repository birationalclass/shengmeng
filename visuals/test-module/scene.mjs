import {refineArchitecture} from './detail.mjs?v=20260920gears1';
import * as T from '../3d/vendor/three.module.js';
import {smooth,clamp,mix,cameraAt,SITES} from './story.mjs?v=20260920detail3';
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
function masonryTexture(){const [c,x]=canvas(512,512),r=rng(413);x.fillStyle='#716653';x.fillRect(0,0,512,512);for(let row=0;row<12;row++)for(let col=-1;col<6;col++){const shade=154+Math.floor(r()*31);x.fillStyle=`rgb(${shade},${shade-10},${shade-29})`;x.fillRect(col*103+(row%2)*51+1,row*43+1,100,40);x.fillStyle='#eee1ba20';x.fillRect(col*103+(row%2)*51+2,row*43+2,98,2);}for(let i=0;i<18000;i++){x.fillStyle=r()>.5?'#fff5db0e':'#271b1013';x.fillRect(r()*512,r()*512,1+r()*2,1);}const t=texture(c);t.wrapS=t.wrapT=T.RepeatWrapping;return t;}
function mapTexture(){const [c,x]=canvas(2048,1024);x.fillStyle='#b9ab8c';x.fillRect(0,0,c.width,c.height);const r=rng(71);for(let i=0;i<48000;i++){x.fillStyle=`rgba(213,192,142,${r()*.04})`;x.fillRect(r()*2048,r()*1024,1+r()*2,1);}
 x.strokeStyle='#54432b38';x.lineWidth=.7;for(let y=30;y<1024;y+=24){x.beginPath();for(let k=0;k<2048;k+=6){const yy=y+30*Math.sin(k*.008+y*.017)+12*Math.sin(k*.023+y*.02);k?x.lineTo(k,yy):x.moveTo(k,yy);}x.stroke();}
 x.strokeStyle='#4c412b55';for(let k=0;k<2048;k+=128){x.beginPath();x.moveTo(k,0);x.lineTo(k,1024);x.stroke();}for(let k=0;k<1024;k+=128){x.beginPath();x.moveTo(0,k);x.lineTo(2048,k);x.stroke();}
 x.font='16px Atlas,serif';x.fillStyle='#493d2daa';x.textAlign='center';for(let i=0;i<15;i++)x.fillText(String(i*15)+'°',i*128+128,34);
 for(const [cx,cy] of [[380,780],[1570,230]]){for(const radius of [50,63,80]){x.beginPath();x.arc(cx,cy,radius,0,TAU);x.stroke();}for(let i=0;i<16;i++){const a=i*TAU/16;x.beginPath();x.moveTo(cx+Math.sin(a)*20,cy+Math.cos(a)*20);x.lineTo(cx+Math.sin(a)*80,cy+Math.cos(a)*80);x.stroke();}x.fillText('N',cx,cy-95);}
 return texture(c);
}
function labelTexture(text,{size=90,sub='',bg='#b4a384',ink='#332b1d',width=1024,height=256}={}){const [c,x]=canvas(width,height);x.fillStyle=bg;x.fillRect(0,0,width,height);x.strokeStyle='#cda96155';x.lineWidth=3;x.strokeRect(12,12,width-24,height-24);x.fillStyle=ink;x.textAlign='center';x.textBaseline='middle';x.font=`${size}px Atlas,'Songti SC',serif`;x.fillText(text,width/2,sub?height*.4:height*.51,width*.89);if(sub){x.font=`${Math.round(size*.28)}px Inter,sans-serif`;x.fillStyle='#c9b995';x.fillText(sub,width/2,height*.77,width*.9);}return texture(c);}
export class AtlasScene{
 constructor(canvas,quality='standard'){
  this.canvas=canvas;this.renderer=new T.WebGLRenderer({canvas,antialias:true,alpha:false,powerPreference:'high-performance'});this.renderer.setClearColor(0x0a1511);this.renderer.outputColorSpace=T.SRGBColorSpace;this.renderer.toneMapping=T.ACESFilmicToneMapping;this.renderer.toneMappingExposure=.94;this.renderer.shadowMap.enabled=true;this.renderer.shadowMap.type=T.PCFSoftShadowMap;
  this.scene=new T.Scene();this.scene.background=new T.Color(0x667e82);this.scene.fog=new T.FogExp2(0x667e82,.0035);this.camera=new T.PerspectiveCamera(40,1,.65,260);this.rotating=[];this.risers=[];this.manual=null;
  this.materials={gold:new T.MeshStandardMaterial({color:color.gold,metalness:.72,roughness:.43}),brass:new T.MeshStandardMaterial({color:color.brass,metalness:.75,roughness:.5}),dark:new T.MeshStandardMaterial({color:color.dark,metalness:.5,roughness:.52}),wood:new T.MeshStandardMaterial({map:woodTexture(),color:0xb9a17d,roughness:.65,metalness:.08}),stone:new T.MeshStandardMaterial({color:0xbbaa87,roughness:.88}),paper:new T.MeshStandardMaterial({color:color.ivory,roughness:.77}),jade:new T.MeshStandardMaterial({color:0x507660,roughness:.57,metalness:.36}),red:new T.MeshStandardMaterial({color:0x9e3922,roughness:.29,metalness:.2}),glow:new T.MeshStandardMaterial({color:0x91d2c6,emissive:0x529d91,emissiveIntensity:1.2,metalness:.38,roughness:.26})};
  const masonry=masonryTexture();this.materials.stone.map=masonry;this.materials.stone.bumpMap=masonry;this.materials.stone.bumpScale=.035;this.materials.stone.color.setHex(0xe8ddc6);this.materials.paving=this.materials.stone.clone();this.materials.paving.map=masonry.clone();this.materials.paving.map.repeat.set(6,6);this.materials.paving.bumpMap=this.materials.paving.map;this.materials.paving.map.needsUpdate=true;
  const env=new T.Scene();env.background=new T.Color(0x4a5549);for(const [p,s,c]of [[[0,14,0],[20,1,18],0xe3d2a7],[[-12,3,8],[1,10,18],0x93b3b0],[[10,5,-8],[1,12,12],0xffffff]]){const m=new T.Mesh(new T.BoxGeometry(...s),new T.MeshBasicMaterial({color:c}));m.position.set(...p);env.add(m);}const pm=new T.PMREMGenerator(this.renderer);this.environment=pm.fromScene(env,.02);this.scene.environment=this.environment.texture;pm.dispose();env.traverse(o=>{o.geometry?.dispose();o.material?.dispose();});
  this.scene.add(new T.HemisphereLight(0xfce8bb,0x36454b,.65));const key=new T.DirectionalLight(0xffe6bd,2.8);key.position.set(-38,62,28);key.castShadow=true;key.shadow.mapSize.set(2048,2048);Object.assign(key.shadow.camera,{left:-85,right:85,top:85,bottom:-85,near:1,far:200});key.shadow.bias=-.00015;key.shadow.normalBias=.09;this.scene.add(key);this.key=key;const fill=new T.DirectionalLight(0xb1c6ce,.85);fill.position.set(6,11,-22);this.scene.add(fill);const rim=new T.DirectionalLight(0xfff0d1,1.1);rim.position.set(25,13,5);this.scene.add(rim);
  this.makeTerrain();
  this.platforms=SITES.map(([x,y,z],i)=>{const p=this.platform(x,i);p.position.z=z;return p;});
  this.makeWriting(this.platforms[0]);this.makePagoda(this.platforms[1]);this.makeNewton(this.platforms[2]);this.makePermutation(this.platforms[3]);this.makeCrystal(this.platforms[4]);this.makeAI(this.platforms[5]);this.makeConnections();refineArchitecture(this);this.makeDust();this.makeOrrery();this.setQuality(quality);this.resize();
 }
 mesh(parent,geometry,material,pos=[0,0,0]){const m=new T.Mesh(geometry,material);m.position.set(...pos);m.castShadow=true;m.receiveShadow=true;parent.add(m);return m;}
 box(parent,size,pos,mat=this.materials.brass){const m=this.mesh(parent,geo('box',()=>new T.BoxGeometry(1,1,1)),mat,pos);m.scale.set(...size);return m;}
 cylinder(parent,r,h,pos,mat=this.materials.brass,r2=r){return this.mesh(parent,geo(`c${r},${r2},${h}`,()=>new T.CylinderGeometry(r,r2,h,48)),mat,pos);}
 torus(parent,r,t,pos,mat=this.materials.gold,rotation=[Math.PI/2,0,0]){const m=this.mesh(parent,geo(`t${r},${t}`,()=>new T.TorusGeometry(r,t,8,96)),mat,pos);m.rotation.set(...rotation);return m;}
 line(parent,points,col=0xc3a875,opacity=.55){const g=new T.BufferGeometry().setFromPoints(points.map(p=>Array.isArray(p)?v(...p):p));const l=new T.Line(g,new T.LineBasicMaterial({color:col,transparent:true,opacity}));parent.add(l);return l;}
 rod(parent,a,b,r=.07,mat=this.materials.gold){const start=v(...a),end=v(...b),d=end.clone().sub(start),m=this.cylinder(parent,r,d.length(),[0,0,0],mat);m.position.copy(start.add(end).multiplyScalar(.5));m.quaternion.setFromUnitVectors(v(0,1,0),d.normalize());return m;}
 plate(parent,text,pos,w=4,h=1,opts={}){const m=this.mesh(parent,new T.PlaneGeometry(w,h),new T.MeshStandardMaterial({map:labelTexture(text,opts),roughness:.63,metalness:.23,transparent:false,polygonOffset:true,polygonOffsetFactor:-1,polygonOffsetUnits:-2}),pos);m.castShadow=false;m.receiveShadow=false;m.rotation.x=-Math.PI/2;return m;}
 gear(parent,r,teeth,pos,speed=.07,mat=this.materials.brass){
  const g=geo(`gear${r}-${teeth}`,()=>{const s=new T.Shape();for(let i=0;i<teeth*4;i++){const a=i*TAU/(teeth*4),rr=r*(i%4===1||i%4===2?1:.87),x=Math.cos(a)*rr,y=Math.sin(a)*rr;i?s.lineTo(x,y):s.moveTo(x,y);}s.closePath();const hole=new T.Path();hole.absarc(0,0,r*.37,0,TAU,true);s.holes.push(hole);return new T.ExtrudeGeometry(s,{depth:.18,bevelEnabled:true,bevelThickness:.025,bevelSize:.025,bevelSegments:1,steps:1});});
  const group=new T.Group();parent.add(group);group.position.set(...pos);const wheel=this.mesh(group,g,mat);wheel.rotation.x=-Math.PI/2;for(let i=0;i<6;i++){const spoke=this.box(group,[r*.72,.16,.10],[Math.cos(i*TAU/6)*r*.53,.09,Math.sin(i*TAU/6)*r*.53],mat);spoke.rotation.y=-i*TAU/6;}this.cylinder(group,r*.16,.28,[0,.06,0],this.materials.gold);group.userData.gear={radius:r,bottom:pos[1]-.08,top:pos[1]+.205};this.rotating.push({object:group,speed});return group;
 }
 platform(x,i){const p=new T.Group();p.position.x=x;this.scene.add(p);this.cylinder(p,7.65,.6,[0,-.55,0],this.materials.dark);this.cylinder(p,7.38,.23,[0,-.16,0],this.materials.brass);this.cylinder(p,7.08,.27,[0,.04,0],this.materials.paving);this.torus(p,7.22,.08,[0,.15,0]);this.torus(p,6.78,.045,[0,.24,0]);
  const ticks=new T.InstancedMesh(geo('tick',()=>new T.BoxGeometry(.035,.04,.22)),this.materials.gold,120),o=new T.Object3D();for(let k=0;k<120;k++){const a=k*TAU/120;o.position.set(Math.sin(a)*7,.22,Math.cos(a)*7);o.rotation.y=a;o.scale.set(1,1,k%5===0?1.8:1);o.updateMatrix();ticks.setMatrixAt(k,o.matrix);}p.add(ticks);
  // An exposed drive sits beyond the masonry footprint, on its own metal bracket.
  const drive=new T.Group();p.add(drive);drive.position.set(-8.95,0,2.5);drive.userData.drivePod=true;
  this.box(drive,[2.65,.18,2.65],[0,-.02,0],this.materials.dark);
  for(const z of [-.85,.85])this.box(drive,[2.2,.14,.14],[1.55,-.32,z],this.materials.brass);
  this.cylinder(drive,.23,.22,[0,.18,0],this.materials.brass);
  this.cylinder(drive,.105,.64,[0,.37,0],this.materials.gold);
  this.gear(drive,1.02,24,[0,.40,0],i%2?-.12:.12);
  this.cylinder(drive,.17,.075,[0,.71,0],this.materials.dark);
  for(const x of [-1.15,1.15])for(const z of [-1.15,1.15])this.cylinder(drive,.06,.045,[x,.095,z],this.materials.gold);
  this.makeRamparts(p,i);this.makeNameplate(p,i);
  for(let j=0;j<10;j++){const a=j*TAU/10;this.cylinder(p,.07,.07,[Math.sin(a)*7.28,.21,Math.cos(a)*7.28],this.materials.gold);}
  return p;
 }
 makeWriting(p){
  const g=new T.Group();p.add(g);this.writing=g;this.risers.push({object:g,start:11,end:19});
  this.box(g,[10,.45,6.6],[0,.52,-.3],this.materials.dark);this.box(g,[9.65,.13,6.25],[0,.82,-.3],this.materials.wood);
  const letters=['山','川','日','月','W','O','R','D'];this.letters=[];
  letters.forEach((c,i)=>{const x=(i%4-1.5)*1.62,z=i<4?-1.65:.7,tile=new T.Group();tile.position.set(x,1,z);g.add(tile);this.box(tile,[1.34,.38,1.45],[0,0,0],this.materials.brass);this.box(tile,[1.22,.07,1.34],[0,.23,0],this.materials.dark);this.plate(tile,c,[0,.273,0],1.13,1.23,{size:148,width:256,height:256,ink:'#ead8a7'});for(const s of [-1,1])this.cylinder(g,.095,.9,[x+s*.45,.9,z],this.materials.gold);this.letters.push({object:tile,x,z,i});});
  this.plate(g,'山 川 · WORD',[0,.91,2.16],7.2,.57,{size:66,width:1024,height:128});
  // The exterior drive replaces decorative wheels intersecting the archive columns.
  for(const x of [-4.4,4.4]){this.cylinder(g,.17,3.15,[x,2.05,-2.85],this.materials.brass);this.cylinder(g,.28,.16,[x,3.66,-2.85],this.materials.gold);}this.rod(g,[-4.4,3.65,-2.85],[4.4,3.65,-2.85],.11,this.materials.brass);
  const page=this.plate(g,'Σ⁺',[0,2.45,-2.82],2.5,1.25,{size:133,width:512,height:256,sub:'THE ART OF CONCATENATION'});page.rotation.x=0;
  for(let j=0;j<18;j++){const x=-3.7+(j%9)*.92,z=-4.45+Math.floor(j/9)*.66;this.box(g,[.75,.13,.5],[x,.39,z],this.materials.dark);this.plate(g,String.fromCharCode(65+j),[x,.46,z],.52,.4,{size:90,width:128,height:128});}
  const book=new T.Group();g.add(book);book.position.set(4.55,1.1,2.8);book.rotation.y=-.28;for(const sign of [-1,1]){const half=this.box(book,[1.0,.15,1.55],[sign*.5,.1,0],this.materials.paper);half.rotation.z=-sign*.13;for(let j=0;j<7;j++)this.rod(book,[sign*.14,.22,-.52+j*.16],[sign*.88,.22,-.52+j*.16],.008,this.materials.brass);}
 }
 makeNewton(p){
  const g=new T.Group();p.add(g);this.tree=g;this.risers.push({object:g,start:69,end:77});this.gear(g,3.2,44,[0,.29,0],.05,this.materials.dark);this.cylinder(g,.22,.18,[0,.51,0],this.materials.brass);this.cylinder(g,2.8,.10,[0,.60,0],this.materials.brass);this.cylinder(g,2.7,.24,[0,.77,0],this.materials.wood);
  const tips=[];const r=rng(1234);const branch=(a,b,thickness,depth)=>{const mid=a.clone().lerp(b,.5);mid.x+=(r()-.5)*.6;mid.z+=(r()-.5)*.6;const curve=new T.CatmullRomCurve3([a,mid,b]);this.mesh(g,new T.TubeGeometry(curve,8,thickness,7,false),depth>1?this.materials.wood:this.materials.brass);
   if(depth===0){tips.push(b);return;}const n=depth===3?4:3;for(let j=0;j<n;j++){const angle=j*TAU/n+r()*1.9,len=1.1+depth*.47,end=b.clone().add(v(Math.cos(angle)*len*.73,.65+r()*1.0,Math.sin(angle)*len*.73));branch(b,end,thickness*.58,depth-1);}};
  branch(v(0,.8,0),v(.15,3.7,0),.46,3);
  const leafG=geo('leaf',()=>new T.IcosahedronGeometry(.22,1)),leaves=new T.InstancedMesh(leafG,this.materials.jade,tips.length*9),o=new T.Object3D();let count=0;
  for(const tip of tips)for(let j=0;j<9;j++){o.position.copy(tip).add(v((r()-.5)*1.35,(r()-.5)*.7,(r()-.5)*1.35));o.rotation.set(r()*Math.PI,r()*TAU,r()*Math.PI);o.scale.set(1.65+r(),.13,.6+r()*.45);o.updateMatrix();leaves.setMatrixAt(count,o.matrix);leaves.setColorAt(count,new T.Color().setHSL(.11+r()*.11,.2+r()*.15,.25+r()*.18));count++;}leaves.castShadow=true;g.add(leaves);
  const appleGeometry=new T.SphereGeometry(.31,24,18);const pos=appleGeometry.attributes.position;for(let i=0;i<pos.count;i++){const x=pos.getX(i),y=pos.getY(i),z=pos.getZ(i),theta=Math.atan2(z,x),bulge=1+.05*Math.cos(theta*5);pos.setXYZ(i,x*bulge,y*(.9+.06*Math.cos(theta*5)),z*bulge);}appleGeometry.computeVertexNormals();
  this.apples=[];for(let j=0;j<9;j++){const tip=tips[Math.floor(j*tips.length/9)],a=new T.Group();a.position.copy(tip).add(v(0,-.52,0));this.mesh(a,appleGeometry,this.materials.red);this.rod(a,[0,.24,0],[.025,.45,0],.035,this.materials.wood);g.add(a);this.apples.push(a);}this.fallingApple=this.apples[4];this.appleOrigin=this.fallingApple.position.clone();
  this.torus(g,3.85,.04,[0,1.1,0],this.materials.gold,[.25,0,0]);const orbit=new T.Group();g.add(orbit);orbit.position.set(0,2.1,0);this.torus(orbit,4.6,.035,[0,0,0],this.materials.gold,[.6,.35,.1]);this.rotating.push({object:orbit,speed:.028});this.orbit=orbit;
  // A seated, deliberately sculptural Newton figure; the apple never hits him.
  const man=new T.Group();g.add(man);man.position.set(-3.1,.85,2.2);man.rotation.y=.3;this.box(man,[1.45,.17,.55],[0,.4,0],this.materials.wood);for(const x of [-.55,.55])this.box(man,[.1,.6,.45],[x,.04,0],this.materials.brass);const coat=this.mesh(man,new T.ConeGeometry(.36,1.25,12),this.materials.dark,[0,1.07,0]);coat.rotation.x=-.15;this.mesh(man,geo('head',()=>new T.SphereGeometry(.25,16,12)),this.materials.paper,[0,1.85,.03]);for(const x of [-.17,.17]){this.rod(man,[x,.74,.02],[x,.48,.65],.115,this.materials.dark);this.rod(man,[x,.48,.65],[x,-.15,.7],.08,this.materials.dark);}this.box(man,[.55,.06,.47],[.05,.96,.61],this.materials.paper);
  // Ivory curls, coat sleeves and a writing hand identify the miniature scholar.
  for(const side of [-1,1]){this.rod(man,[side*.27,1.47,.04],[side*.43,1.13,.30],.10,this.materials.dark);this.rod(man,[side*.43,1.13,.30],[side*.19,1.03,.61],.075,this.materials.dark);this.mesh(man,new T.SphereGeometry(.085,10,8),this.materials.paper,[side*.19,1.03,.61]);for(let j=0;j<4;j++){const curl=this.mesh(man,new T.SphereGeometry(.12,10,8),this.materials.paper,[side*.22,1.98-j*.115,-.1]);curl.scale.set(.8,1.2,1.0);}}for(let j=0;j<3;j++)this.mesh(man,new T.SphereGeometry(.025,8,6),this.materials.gold,[0,1.34-j*.15,.2]);
  const house=new T.Group();this.manor=house;g.add(house);house.position.set(3.8,.25,-3.3);this.box(house,[2.0,1.5,1.45],[0,.75,0],this.materials.stone);const roof=this.mesh(house,new T.ConeGeometry(1.7,1.1,4),this.materials.dark,[0,2.0,0]);roof.rotation.y=Math.PI/4;roof.scale.z=.8;for(const x of [-.62,0,.62])for(const y of [.5,1.1])this.box(house,[.22,.32,.035],[x,y,.745],this.materials.gold);this.box(house,[.22,.85,.25],[.7,2.12,-.25],this.materials.stone);

 }
 makeAI(p){
  const g=new T.Group();p.add(g);this.ai=g;this.risers.push({object:g,start:159,end:168});this.cylinder(g,3.5,.3,[0,.5,0],this.materials.dark);this.torus(g,3.45,.055,[0,.67,0]);
  const layers=[5,7,7,5],nodes=[],all=[];for(let l=0;l<4;l++){const x=-3.75+l*2.5;const layer=[];this.box(g,[.7,.12,5.3],[x,.47,0],this.materials.brass);for(let j=0;j<layers[l];j++){const angle=j*TAU/layers[l]+.3*l,pt=v(x,3.8+Math.sin(angle)*2.1,Math.cos(angle)*2.1);layer.push(pt);all.push({pt,l,j});}nodes.push(layer);const arch=this.torus(g,2.75,.055,[x,3.8,0],this.materials.gold,[0,Math.PI/2,0]);for(const z of [-2,2])this.rod(g,[x,.6,z],[x,3.8,z*1.37],.065,this.materials.brass);}
  const nodeGeometry=geo('node',()=>new T.IcosahedronGeometry(.19,1));this.neurons=all.map(({pt,l,j})=>({mesh:this.mesh(g,nodeGeometry,this.materials.glow,pt.toArray()),l,j}));
  const segments=[];this.synapses=[];for(let l=0;l<3;l++)for(let i=0;i<nodes[l].length;i++)for(let j=0;j<nodes[l+1].length;j++){const a=nodes[l][i],b=nodes[l+1][j];segments.push(...a.toArray(),...b.toArray());this.synapses.push({a,b,l,offset:(i*3+j)*.079});}
  const geoLines=new T.BufferGeometry();geoLines.setAttribute('position',new T.Float32BufferAttribute(segments,3));this.neuralLines=new T.LineSegments(geoLines,new T.LineBasicMaterial({color:0xc9af76,transparent:true,opacity:.20}));g.add(this.neuralLines);
  this.pulses=new T.InstancedMesh(geo('pulse',()=>new T.SphereGeometry(.047,6,4)),new T.MeshBasicMaterial({color:0x9cfff0}),this.synapses.length);g.add(this.pulses);this.pulses.frustumCulled=false;
  for(let j=0;j<12;j++){const a=j*TAU/12;const server=this.box(g,[.45,.7+rand()*.9,.55],[Math.sin(a)*5.35,.8,Math.cos(a)*5.35],this.materials.dark);for(let k=0;k<4;k++)this.box(server,[.64,.025,.07],[0,-.25+k*.14,.51],this.materials.gold);}
  // The server ring stays clear; its visible drive is on the external bracket.
  const core=new T.Group();g.add(core);core.position.set(0,4,0);for(let j=0;j<3;j++)this.torus(core,1.1+j*.3,.025,[0,0,0],this.materials.gold,[j*.8,j*.6,j*.4]);this.rotating.push({object:core,speed:.18});
 }
 makeTerrain(){
  const sea=new T.Mesh(new T.PlaneGeometry(900,900),new T.MeshStandardMaterial({color:0x6a858b,roughness:.63,metalness:.24}));sea.rotation.x=-Math.PI/2;sea.position.y=-2.9;sea.receiveShadow=true;this.scene.add(sea);
  const coast=[[-49,-34],[-34,-48],[-12,-52],[13,-49],[28,-41],[43,-30],[46,-12],[40,4],[28,15],[15,19],[6,38],[-10,34],[-22,17],[-35,11],[-43,0],[-49,-15]],shape=new T.Shape();coast.forEach(([x,z],i)=>i?shape.lineTo(x*1.4,-z*1.4):shape.moveTo(x*1.4,-z*1.4));shape.closePath();
  for(let i=0;i<3;i++){const g=new T.ExtrudeGeometry(shape,{depth:.42,bevelEnabled:true,bevelThickness:.09,bevelSize:.12,bevelSegments:1,steps:1}),m=this.mesh(this.scene,g,i===1?this.materials.brass:this.materials.stone);m.rotation.x=-Math.PI/2;m.position.y=-2.15+i*.49;m.scale.setScalar(1+(2-i)*.009);}
  const top=new T.ShapeGeometry(shape);const pos=top.attributes.position,uv=top.attributes.uv;for(let i=0;i<pos.count;i++)uv.setXY(i,(pos.getX(i)+70)/140,(pos.getY(i)+42)/119);const m=new T.Mesh(top,new T.MeshStandardMaterial({map:mapTexture(),roughness:.87,metalness:.07}));m.rotation.x=-Math.PI/2;m.position.y=-.54;m.receiveShadow=true;this.scene.add(m);
  const riverPoints=[[-14,18],[-7,18],[7,11],[14,5],[13,0],[4,6],[-8,13],[-17,14]],riverShape=new T.Shape();riverPoints.forEach(([x,z],i)=>i?riverShape.lineTo(x*1.4,-z*1.4):riverShape.moveTo(x*1.4,-z*1.4));riverShape.closePath();const river=new T.Mesh(new T.ShapeGeometry(riverShape),new T.MeshStandardMaterial({color:0x6a858b,roughness:.36,metalness:.28}));river.rotation.x=-Math.PI/2;river.position.y=-.52;this.scene.add(river);
  // Small relief mountain ranges and engraved longitudinal lines on a cut coastline.
  const random=rng(57);for(let i=0;i<36;i++){const x=-37+i*1.5,z=-32+Math.sin(i*.22)*3,h=.55+random()*1.5;const mountain=this.mesh(this.scene,new T.ConeGeometry(.5+random()*.7,h,4),this.materials.stone,[x*1.4,-.5+h/2,z*1.4]);mountain.rotation.y=.5+random();}
 }
 makeRamparts(p,i){
  this.architecture??=[];const start=[11,39,69,99,129,159][i];
  for(let j=0;j<8;j++){const a=(j/8)*TAU,r=6.0,g=new T.Group();p.add(g);g.position.set(Math.sin(a)*r,0,Math.cos(a)*r);g.rotation.y=a;
   if(i===0){this.box(g,[.55,1.55,.55],[0,.95,0],this.materials.stone);this.box(g,[.85,.25,.8],[0,1.85,0],this.materials.stone);}
   else if(i===1){this.cylinder(g,.14,1.55,[0,1,0],this.materials.wood);this.box(g,[.9,.16,.46],[0,1.7,0],this.materials.wood);this.mesh(g,new T.ConeGeometry(.67,.4,4),this.materials.dark,[0,2.05,0]).rotation.y=Math.PI/4;}
   else if(i===2){this.box(g,[.72,.85,.65],[0,.65,0],this.materials.stone);this.mesh(g,new T.ConeGeometry(.69,.6,4),this.materials.dark,[0,1.36,0]).rotation.y=Math.PI/4;this.box(g,[.16,.28,.03],[0,.7,.34],this.materials.dark);}
   else if(i===3){this.cylinder(g,.2,1.65,[0,1.05,0],this.materials.stone);this.cylinder(g,.32,.15,[0,1.9,0],this.materials.stone);}
   else if(i===4){this.box(g,[.16,2.6,.16],[0,1.5,0],this.materials.dark);for(const sign of [-1,1])this.rod(g,[0,.3,0],[sign*.6,2.7,0],.045,this.materials.brass);}
   else{const h=1.5+(j%3)*.8;this.box(g,[.5,h,.5],[0,h/2+.25,0],this.materials.dark);for(let k=0;k<5;k++)this.box(g,[.35,.04,.03],[0,.55+k*.25,.26],this.materials.gold);}
   this.architecture.push({g,start:start+j*.16,end:start+5+j*.16});
  }
 }
 makeNameplate(p,i){
  const en=['SEMIGROUP','CHINESE REMAINDER THEOREM','ACTION','GALOIS','SYMMETRY','COMPOSITION'][i],zh=['半群','中国剩余定理','作用','伽罗瓦','对称','复合'][i];
  const plaque=new T.Group();p.add(plaque);plaque.position.set(0,-.27,10.0);plaque.rotation.y=-.1;
  this.box(plaque,[11.9,.32,2.55],[0,0,0],this.materials.brass);this.box(plaque,[11.56,.11,2.24],[0,.20,0],this.materials.stone);
  const [c,x]=canvas(1536,320);x.fillStyle='#cbb997';x.fillRect(0,0,1536,320);x.strokeStyle='#635034';x.lineWidth=3;x.strokeRect(17,17,1502,286);x.lineWidth=1;x.strokeRect(25,25,1486,270);x.fillStyle='#403321';x.textAlign='center';x.textBaseline='middle';x.font=`${i===1?60:91}px Atlas,serif`;x.fillText(en,768,119,1390);x.font="45px 'Songti SC',serif";x.fillText(zh,768,226,1370);
  const face=this.mesh(plaque,new T.PlaneGeometry(11.45,2.13),new T.MeshStandardMaterial({map:texture(c),roughness:.82,metalness:.05,polygonOffset:true,polygonOffsetFactor:-1,polygonOffsetUnits:-2}),[0,.285,0]);face.rotation.x=-Math.PI/2;face.castShadow=false;face.receiveShadow=false;
  for(const xx of [-5.58,5.58])for(const zz of [-.93,.93])this.cylinder(plaque,.065,.055,[xx,.28,zz],this.materials.brass);
 }
 makeChineseHouses(p){
  const group=new T.Group();p.add(group);this.risers.push({object:group,start:45,end:52});
  const wall=new T.MeshStandardMaterial({color:0xc5b99c,roughness:.88}),wood=new T.MeshStandardMaterial({color:0x694329,roughness:.78});
  // A low courtyard hall with white walls and a pitched, upturned tiled roof.
  const hall=new T.Group();this.chineseHall=hall;group.add(hall);hall.position.set(2.2,.3,-1.1);hall.rotation.y=-.15;this.box(hall,[3.0,1.6,1.75],[0,.83,0],wall);this.box(hall,[3.3,.18,2.05],[0,.02,0],this.materials.stone);
  for(const sign of [-1,1]){const roof=this.box(hall,[3.75,.13,1.35],[0,1.91,sign*.49],this.materials.dark);roof.rotation.x=sign*.28;this.rod(hall,[-1.85,1.79,sign*1.16],[1.85,1.79,sign*1.16],.07,wood);}this.rod(hall,[-1.86,2.12,0],[1.86,2.12,0],.08,this.materials.dark);
  this.box(hall,[.62,1.22,.04],[0,.72,.90],wood);for(const xx of [-1.05,1.05]){this.box(hall,[.63,.69,.05],[xx,1.06,.90],wood);for(let k=-2;k<=2;k++)this.box(hall,[.03,.59,.02],[xx+k*.11,1.06,.935],this.materials.stone);}for(const xx of [-1.2,1.2])this.box(hall,[.12,1.52,.12],[xx,.78,1.16],wood);
  const pavilion=new T.Group();this.pavilion=pavilion;group.add(pavilion);pavilion.position.set(2.65,.2,3.15);this.cylinder(pavilion,1.3,.2,[0,.18,0],this.materials.stone);for(let j=0;j<6;j++){const a=j*TAU/6;this.cylinder(pavilion,.075,1.7,[Math.sin(a)*.91,1.10,Math.cos(a)*.91],wood);}this.mesh(pavilion,new T.ConeGeometry(1.53,.72,6),this.materials.dark,[0,2.2,0]);this.mesh(pavilion,new T.SphereGeometry(.09,10,8),this.materials.gold,[0,2.64,0]);
  for(const xx of [-.1,4.25])this.box(group,[.16,.68,3.4],[xx,.67,1.7],wall);for(let j=0;j<5;j++)this.box(group,[.67,.05,.37],[1.1,.37,1.2+j*.45],this.materials.stone);
 }
 makeCathedral(g){
  const church=new T.Group();this.cathedral=church;g.add(church);church.position.set(0,.82,-.85);const stone=this.materials.stone,roof=this.materials.dark;
  this.box(church,[3.5,2.6,4.4],[0,1.3,-.6],stone);this.box(church,[4.0,.2,4.9],[0,-.05,-.6],stone);
  for(const sign of [-1,1]){const panel=this.box(church,[2.04,.16,4.7],[sign*.78,3.22,-.6],roof);panel.rotation.z=-sign*.65;}
  this.rod(church,[0,3.86,-3],[0,3.86,1.8],.06,this.materials.brass);
  // Twin western towers, a rose window, pointed portals and flying buttresses.
  for(const sign of [-1,1]){const tower=new T.Group();church.add(tower);tower.position.set(sign*1.62,0,1.48);this.box(tower,[1.13,4.7,1.1],[0,2.35,0],stone);this.box(tower,[1.29,.18,1.24],[0,4.77,0],stone);for(const xx of [-.35,.35])for(const zz of [-.35,.35]){this.cylinder(tower,.075,.5,[xx,5.0,zz],stone);this.mesh(tower,new T.ConeGeometry(.12,.43,6),stone,[xx,5.46,zz]);}for(const xx of [-.24,.24]){this.box(tower,[.17,1.15,.035],[xx,3.8,.564],roof);this.mesh(tower,new T.ConeGeometry(.105,.24,3),roof,[xx,4.48,.565]).rotation.x=Math.PI/2;}}
  this.box(church,[2.2,3.5,.35],[0,1.75,1.89],stone);const rose=this.mesh(church,new T.CircleGeometry(.53,48),roof,[0,2.62,2.083]);this.torus(church,.56,.055,[0,2.62,2.09],this.materials.brass,[0,0,0]);for(let j=0;j<12;j++){const a=j*TAU/12;this.rod(church,[0,2.62,2.11],[Math.cos(a)*.51,2.62+Math.sin(a)*.51,2.11],.018,stone);}
  for(const xx of [-.7,0,.7]){this.box(church,[.48,1.23,.045],[xx,.65,2.09],roof);const shape=new T.Shape();shape.moveTo(-.24,0);shape.quadraticCurveTo(-.17,.35,0,.52);shape.quadraticCurveTo(.17,.35,.24,0);shape.closePath();this.mesh(church,new T.ShapeGeometry(shape),roof,[xx,1.24,2.12]);}
  for(const sign of [-1,1])for(let j=0;j<4;j++){const z=-2.5+j*1.02;this.box(church,[.24,1.8,.26],[sign*2.1,.9,z],stone);this.rod(church,[sign*2.1,1.75,z],[sign*1.6,2.7,z],.095,stone);this.mesh(church,new T.ConeGeometry(.16,.7,4),stone,[sign*2.1,2.2,z]);}
 }

 makePagoda(p){
  const g=new T.Group();p.add(g);this.pagoda=g;g.scale.setScalar(.62);g.position.set(-1.7,0,-.7);this.pagodaFloors=[];this.makeChineseHouses(p);this.cylinder(g,4.6,.30,[0,.37,0],this.materials.stone);this.gear(g,4.2,56,[0,.65,0],.07);this.cylinder(g,.24,.48,[0,.78,0],this.materials.brass);
  const timber=new T.MeshStandardMaterial({color:0x774325,roughness:.7,metalness:.12}),roofMat=new T.MeshStandardMaterial({color:0x485b51,roughness:.64,metalness:.3});
  for(let floor=0;floor<5;floor++){const level=new T.Group(),w=3.5-floor*.49,y=1.05+floor*1.67;g.add(level);this.pagodaFloors.push({level,y,start:41+floor*2.8,end:44+floor*2.8});
   this.box(level,[w*2,.17,w*2],[0,0,0],timber);for(const x of [-w*.78,w*.78])for(const z of [-w*.78,w*.78]){this.cylinder(level,.11,1.18,[x,.64,z],timber);this.box(level,[.53,.12,.35],[x,1.17,z],timber);this.box(level,[.36,.13,.58],[x,1.3,z],this.materials.brass);}
   for(const sign of [-1,1]){this.box(level,[w*1.7,.16,.13],[0,1.22,sign*w*.78],timber);this.box(level,[.13,.16,w*1.7],[sign*w*.78,1.22,0],timber);for(let j=-2;j<=2;j++){this.box(level,[.055,.48,.055],[j*w*.3,.36,sign*w*.93],timber);this.box(level,[.055,.48,.055],[sign*w*.93,.36,j*w*.3],timber);}this.box(level,[w*1.9,.075,.09],[0,.59,sign*w*.93],timber);this.box(level,[.09,.075,w*1.9],[sign*w*.93,.59,0],timber);}
   // Four curved roof faces with lifted eaves and layered timber brackets.
   const roofRoot=new T.Group();level.add(roofRoot);this.pagodaFloors.at(-1).roofRoot=roofRoot;const vertices=[],indices=[];for(let side=0;side<4;side++){const base=vertices.length/3;for(let ring=0;ring<=6;ring++){const u=ring/6,extent=w*1.12*(1-u*.74),height=1.23+.53*u*u+.16*(1-u)**5;for(let j=0;j<=12;j++){const q=-1+j/6,x=q*extent,z=extent,angle=side*Math.PI/2;vertices.push(x*Math.cos(angle)-z*Math.sin(angle),height+.09*Math.abs(q)**6*(1-u),x*Math.sin(angle)+z*Math.cos(angle));}}for(let a=0;a<6;a++)for(let b=0;b<12;b++){const k=base+a*13+b;indices.push(k,k+13,k+1,k+1,k+13,k+14);}}
   const geometry=new T.BufferGeometry();geometry.setAttribute('position',new T.Float32BufferAttribute(vertices,3));geometry.setIndex(indices);geometry.computeVertexNormals();const roof=this.mesh(roofRoot,geometry,roofMat);roof.material.side=T.DoubleSide;

  }
  const finial=new T.Group();this.pagodaFloors[4].level.add(finial);this.cylinder(finial,.075,.85,[0,2,0],this.materials.gold);this.mesh(finial,new T.SphereGeometry(.17,12,10),this.materials.gold,[0,2.48,0]);
 }

 makePermutation(p){
  const g=new T.Group();p.add(g);this.risers.push({object:g,start:99,end:107});this.permutation=g;
  this.gear(g,3.3,48,[0,.29,0],.12);this.cylinder(g,.24,.20,[0,.52,0],this.materials.brass);this.cylinder(g,2.85,.27,[0,.69,0],this.materials.stone);
  this.makeCathedral(g);
  this.roots=[];for(let i=0;i<3;i++){const root=new T.Group();g.add(root);const mat=new T.MeshStandardMaterial({color:[0xeee2bc,0x698987,0xa87842][i],metalness:.65,roughness:.26});this.mesh(root,new T.SphereGeometry(.48,24,16),mat,[0,.7,0]);this.cylinder(root,.16,.7,[0,.14,0]);this.torus(root,.68,.03,[0,.15,0]);this.plate(root,['α','αω','αω²'][i],[0,.18,.95],1.3,.5,{size:80,width:256,height:128});this.roots.push(root);}
  this.torus(g,4.3,.045,[0,1.1,0]);this.torus(g,4.6,.035,[0,1.1,0]);
 }
 makeCrystal(p){
  const g=new T.Group();p.add(g);this.crystal=g;this.risers.push({object:g,start:129,end:137});this.gear(g,3.3,48,[0,.4,0],-.10);
  const mat=new T.MeshPhysicalMaterial({color:0xb5cfca,metalness:.3,roughness:.2,clearcoat:1,clearcoatRoughness:.14,flatShading:true});this.crystalInstances=new T.InstancedMesh(new T.OctahedronGeometry(.53),mat,27);g.add(this.crystalInstances);this.crystalInstances.frustumCulled=false;this.crystalNodes=[];
  const lines=[];for(let x=-1;x<=1;x++)for(let y=0;y<3;y++)for(let z=-1;z<=1;z++){const a=[x*2.25,1.35+y*2.25,z*2.25];this.crystalNodes.push(a);for(let axis=0;axis<3;axis++)if([x,y,z][axis]<(axis===1?2:1)){const b=[...a];b[axis]+=2.25;lines.push(...a,...b);}}
  const geometry=new T.BufferGeometry();geometry.setAttribute('position',new T.Float32BufferAttribute(lines,3));const bonds=new T.LineSegments(geometry,new T.LineBasicMaterial({color:0x70512b,transparent:true,opacity:.7}));g.add(bonds);
  for(const z of [-3.4,0,3.4]){const pts=[];for(let j=0;j<=24;j++){const a=j*Math.PI/24;pts.push(v(Math.cos(a)*3.7,3.6+Math.sin(a)*3.2,z));}const curve=new T.CatmullRomCurve3(pts);this.mesh(g,new T.TubeGeometry(curve,32,.07,6,false),this.materials.dark);for(const x of [-3.7,3.7])this.rod(g,[x,.5,z],[x,3.6,z],.09,this.materials.dark);}for(const x of [-3.7,0,3.7])this.rod(g,[x,x===0?6.8:3.6,-3.4],[x,x===0?6.8:3.6,3.4],.065,this.materials.brass);
  const frame=new T.BoxGeometry(4.5,4.5,4.5),edges=new T.LineSegments(new T.EdgesGeometry(frame),new T.LineBasicMaterial({color:0xead8a6}));edges.position.set(0,3.6,0);g.add(edges);
  for(const x of [-3.6,3.6])for(const z of [-3.6,3.6]){this.cylinder(g,.22,4.7,[x,2.75,z]);this.mesh(g,new T.ConeGeometry(.48,.6,4),this.materials.stone,[x,5.4,z]);}
 }
 animateNewScenes(t){
  for(const {level,y,start,end,roofRoot}of this.pagodaFloors){const u=smooth((t-start)/(end-start));level.visible=u>.001;level.position.y=y-(1-u)*1.3;const roofU=smooth((t-start-1.2)/1.8);roofRoot.visible=roofU>.001;roofRoot.position.y=(1-roofU)*1.8;}
  for(const {g,leaves,chains,length,start,end}of this.bridges){const u=smooth((t-start)/(end-start)),angle=-(1-u)*1.08;for(const pivot of leaves)pivot.rotation.x=angle;g.updateMatrixWorld(true);for(const {line,pivot,x,sign,half}of chains){const tip=pivot.localToWorld(v(x,.15,half));g.worldToLocal(tip);const a=line.geometry.attributes.position;a.setXYZ(0,x,3.4,sign*length/2);a.setXYZ(1,tip.x,tip.y,tip.z);a.needsUpdate=true;line.geometry.computeBoundingSphere();}}

  for(const {g,start,end}of this.architecture){const amount=smooth((t-start)/(end-start));g.position.y=-3.5*(1-amount);g.scale.y=1;g.visible=amount>.001;}
  // A 3-cycle, then a transposition. Intermediate positions illustrate motion,
  // only their endpoints are permutations of the displayed root positions.
  const cycle=smooth((t-109)/6)*TAU/3,swap=smooth((t-119)/5),base=this.roots.map((_,i)=>{const a=i*TAU/3+cycle;return v(Math.sin(a)*4.3,1.1,Math.cos(a)*4.3);});
  this.roots.forEach((root,i)=>{const j=i<2?1-i:i;root.position.copy(base[i]).lerp(base[j],i<2?swap:0);if(i<2)root.position.y+=Math.sin(swap*Math.PI)*(i===0?1.7:-.6);});
  const o=new T.Object3D();this.crystalNodes.forEach(([x,y,z],i)=>{const grow=smooth((t-135-(Math.abs(x)+Math.abs(z)+y)*.24)/3);o.position.set(x,y,z);o.rotation.set(0,Math.PI/4,0);o.scale.setScalar(Math.max(.001,grow));o.updateMatrix();this.crystalInstances.setMatrixAt(i,o.matrix);});this.crystalInstances.instanceMatrix.needsUpdate=true;
 }

 makeConnections(){
  this.bridges=[];
  for(let i=0;i<SITES.length-1;i++){
   const from=v(...SITES[i]),to=v(...SITES[i+1]),delta=to.clone().sub(from),length=delta.length()-21.4,direction=delta.normalize(),g=new T.Group();g.position.copy(from.clone().add(to).multiplyScalar(.5));g.rotation.y=Math.atan2(direction.x,direction.z);this.scene.add(g);
   const leaves=[],chains=[];
   for(const sign of [-1,1]){
    // A separate pier reaches out beyond the round city; hinges live at its tip.
    this.box(g,[3.0,.35,3.6],[0,.03,sign*(length/2+1.8)],this.materials.stone);for(let k=0;k<10;k++)this.box(g,[2.75,.10,.31],[0,.255,sign*(length/2+.18+k*.36)],this.materials.wood);for(const x of [-1.3,1.3])this.box(g,[.12,.33,3.65],[x,.29,sign*(length/2+1.8)],this.materials.brass);
    for(const x of [-1.38,1.38]){this.box(g,[.32,4.1,.35],[x,1.45,sign*length/2],this.materials.wood);this.cylinder(g,.26,.18,[x,3.54,sign*length/2],this.materials.brass);this.box(g,[.5,.42,.54],[x,-.43,sign*length/2],this.materials.stone);}this.box(g,[3.2,.23,.3],[0,3.45,sign*length/2],this.materials.wood);
    const pivot=new T.Group();g.add(pivot);pivot.position.set(0,.22,sign*length/2);pivot.rotation.order='YXZ';pivot.rotation.y=sign===1?Math.PI:0;leaves.push(pivot);
    const half=length/2;for(let j=0;j<Math.ceil(half/.36);j++)this.box(pivot,[2.45,.14,.30],[0,0,(j+.5)*half/Math.ceil(half/.36)],this.materials.wood);
    for(const x of [-1.1,1.1]){this.box(pivot,[.12,.19,half],[x,-.08,half/2],this.materials.brass);for(let j=0;j<=4;j++)this.box(pivot,[.08,.75,.08],[x,.43,half*j/4],this.materials.wood);this.rod(pivot,[x,.8,0],[x,.8,half],.055,this.materials.brass);
     const geometry=new T.BufferGeometry();geometry.setAttribute('position',new T.Float32BufferAttribute(new Float32Array(6),3));const line=new T.Line(geometry,new T.LineBasicMaterial({color:0x302a20}));g.add(line);chains.push({line,pivot,x,sign,half});}
    this.box(g,[1.72,.14,1.72],[-2.45,.04,sign*length/2],this.materials.dark);
    for(const dz of [-.5,.5])this.box(g,[1.5,.12,.12],[-1.9,-.10,sign*length/2+dz],this.materials.brass);
    this.cylinder(g,.16,.24,[-2.45,.23,sign*length/2],this.materials.brass);
    this.gear(g,.68,14,[-2.45,.43,sign*length/2],sign*.17);
   }
   // Hanging side cables remain between the two gates while the leaves lower.
   for(const x of [-1.55,1.55]){const pts=[];for(let j=0;j<=28;j++){const u=j/28;pts.push(v(x,3.42-1.48*Math.sin(Math.PI*u),-length/2+length*u));}this.mesh(g,new T.TubeGeometry(new T.CatmullRomCurve3(pts),32,.035,5,false),this.materials.dark);}
   this.bridges.push({g,leaves,chains,length,start:[35,65,95,125,155][i],end:[43,73,103,133,163][i]});
  }
 }

 makeDust(){const r=rng(99),a=[];for(let i=0;i<650;i++)a.push((r()-.5)*90,r()*18,(r()-.5)*45);const g=new T.BufferGeometry();g.setAttribute('position',new T.Float32BufferAttribute(a,3));const [c,x]=canvas(32,32),gradient=x.createRadialGradient(16,16,0,16,16,16);gradient.addColorStop(0,'#ffffee');gradient.addColorStop(.15,'#fff1ce');gradient.addColorStop(1,'#fff0');x.fillStyle=gradient;x.fillRect(0,0,32,32);this.dust=new T.Points(g,new T.PointsMaterial({color:0xf3d5a0,size:.11,map:texture(c),transparent:true,opacity:.45,depthWrite:false,blending:T.AdditiveBlending}));this.scene.add(this.dust);}
 makeOrrery(){const group=new T.Group();group.position.set(-35,12,-21);this.scene.add(group);for(let i=0;i<3;i++){const ring=new T.Group();group.add(ring);ring.rotation.set(.2+i*.7,.3+i*.6,0);this.torus(ring,3.2+i*.7,.08,[0,0,0],this.materials.brass,[0,0,0]);this.rotating.push({object:ring,speed:(i%2?-.07:.09)});}this.mesh(group,new T.SphereGeometry(1.65,32,20),new T.MeshStandardMaterial({color:0xcda86a,emissive:0xaa722a,emissiveIntensity:.5,metalness:.6,roughness:.35}));this.orrery=group;}
 setQuality(q){this.quality=q;this.renderer.setPixelRatio(Math.min(devicePixelRatio||1,q==='high'?2:q==='low'?1:1.5));this.renderer.shadowMap.enabled=q!=='low';const size=q==='high'?4096:2048;if(this.key.shadow.mapSize.x!==size){this.key.shadow.map?.dispose();this.key.shadow.map=null;this.key.shadow.mapSize.set(size,size);}this.resize();}
 resize(){const w=this.canvas.clientWidth||innerWidth,h=this.canvas.clientHeight||innerHeight;this.renderer.setSize(w,h,false);this.camera.aspect=w/h;this.camera.setViewOffset(w,h,0,w<600?-h*.03:0,w,h);this.camera.updateProjectionMatrix();}
 takeControl(){const target=this.currentTarget||v(0,2,0),offset=this.camera.position.clone().sub(target);this.manual={target:target.clone(),radius:offset.length(),theta:Math.atan2(offset.x,offset.z),phi:Math.acos(clamp(offset.y/offset.length(),-1,1))};}
 orbit(dx,dy){if(!this.manual)this.takeControl();this.manual.theta-=dx*.006;this.manual.phi=clamp(this.manual.phi+dy*.004,.23,1.45);}
 zoom(delta){if(!this.manual)this.takeControl();this.manual.radius=clamp(this.manual.radius*Math.exp(delta*.001),10,88);}
 update(t){
  for(const {object,speed}of this.rotating)object.rotation.y=t*speed;
  for(const {object,start,end}of this.risers){const amount=smooth((t-start)/(end-start));object.position.y=-8*(1-amount);object.scale.y=1;object.visible=amount>.002;}
  const join=smooth((t-25)/5);for(const {object,x,z,i}of this.letters){object.position.x=x*(i>=4?mix(1,.86,join):1);object.position.y=1+.14*Math.sin(t*.7+i)*smooth((t-12-i*.45)/3);object.position.z=z;}
  const drop=clamp((t-85)/4),ay=Math.max(.96,this.appleOrigin.y-(this.appleOrigin.y-.96)*drop*drop);this.fallingApple.position.set(this.appleOrigin.x,ay,this.appleOrigin.z);this.fallingApple.rotation.z=drop*.6;
  const o=new T.Object3D();this.synapses.forEach(({a,b,l,offset},i)=>{const progress=((t*.32-l*.27-offset)%1+1)%1;o.position.copy(a).lerp(b,progress);o.scale.setScalar(smooth((t-169)/4)*(.55+.45*Math.sin(Math.PI*progress)));o.updateMatrix();this.pulses.setMatrixAt(i,o.matrix);});this.pulses.instanceMatrix.needsUpdate=true;
  this.neurons.forEach(({mesh,l,j})=>mesh.scale.setScalar(1+.17*Math.sin(t*2.0-l*1.0+j*.5)));this.dust.rotation.y=t*.002;this.dust.position.y=Math.sin(t*.1)*.4;
  const {pos,target,roll}=cameraAt(t,this.camera.aspect);this.currentTarget=v(...target);
  if(this.manual){const {target:aim,radius,theta,phi}=this.manual;this.camera.position.set(aim.x+radius*Math.sin(phi)*Math.sin(theta),aim.y+radius*Math.cos(phi),aim.z+radius*Math.sin(phi)*Math.cos(theta));this.camera.lookAt(aim);}else{this.camera.position.set(...pos);this.camera.lookAt(this.currentTarget);this.camera.rotation.z+=roll;}
  this.animateNewScenes(t);this.renderer.render(this.scene,this.camera);
 }
}
