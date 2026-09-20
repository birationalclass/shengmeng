import {syncWallBeacons} from './board-beacons.mjs?v=wall-gate2';
import {planConstruction} from './construction.mjs?v=owl-clearance1';
import * as T from '../3d/vendor/three.module.js';
import {replaceDomain,enrichDomain,domainMaterials} from './enchanted-domains.mjs?v=owl-clearance1';
import {landmark} from './landmarks.mjs?v=living1';
import {greatWall} from './great-wall.mjs?v=wutong1';
import {THEMES,plaqueOffset} from './journey.mjs?v=owl-clearance1';
const WIDTH=10.8,SIZE=1152,PAD=44;
// Every playable cell is drawn on the same horizontal mesh as the timber board.
// Hit targets are projected from these world coordinates, so orbiting never detaches input.
export function installBoards(a){
 const originals=[null,a.pagoda,a.manor,a.cathedral,a.crystal,a.ai,null,null];originals.forEach(g=>g?.removeFromParent());a.boards=[];a.disks=[];
 a.platforms.forEach((base,i)=>{
  base.clear();const n=i+2,M=a.materials,theme=THEMES[i],trim=M.brass.clone(),frame=M.wood.clone();trim.color.setHex(theme.rim);frame.color.setHex(theme.frame);
  a.cylinder(base,13.05,.62,[0,-.48,0],M.dark);a.cylinder(base,12.9,.15,[0,-.09,0],trim);const disk=a.cylinder(base,12.72,.12,[0,.05,0],M.paving);disk.userData.region=i;a.disks.push(disk);
  const ring=a.torus(base,12.73,.065,[0,.13,0],trim.clone());a.markers[i]=ring;
  for(let k=0;k<96;k++){const q=k*Math.PI/48;a.box(base,[.055,.035,k%4===0?.45:.18],[Math.sin(q)*12.35,.13,Math.cos(q)*12.35],trim).rotation.y=q;}
  const p=new T.Group();base.add(p);p.visible=false;const lift=new T.Group();p.add(lift);lift.position.y=.8;lift.userData.boardLift=true;
  a.box(lift,[11.8,.52,11.8],[0,.40,0],frame);a.box(lift,[11.5,.065,11.5],[0,.69,0],trim);a.box(lift,[11.36,.07,11.36],[0,.75,0],frame);
  // Corner fixtures and ornament vary with the region, while the grid stays clear.
  for(const x of [-5.7,5.7])for(const z of [-5.7,5.7]){
   if(i%3===0){a.cylinder(lift,.13,.08,[x,.72,z],trim);a.torus(lift,.20,.025,[x,.79,z],trim);}
   else if(i%3===1){const gem=a.mesh(lift,new T.OctahedronGeometry(.17),trim,[x,.79,z]);gem.rotation.y=Math.PI/4;}
   else{a.box(lift,[.39,.08,.13],[x,.74,z],trim);a.box(lift,[.13,.08,.39],[x,.74,z],trim);}
  }
  for(let k=0;k<n*4;k++){const q=k*Math.PI*2/(n*4);a.cylinder(lift,.035,.06,[Math.sin(q)*6.45,.23,Math.cos(q)*6.45],trim);}
  const canvas=document.createElement('canvas');canvas.width=canvas.height=SIZE;const texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;texture.anisotropy=Math.min(8,a.renderer.capabilities.getMaxAnisotropy());
  const mesh=new T.Mesh(new T.PlaneGeometry(WIDTH,WIDTH),new T.MeshStandardMaterial({map:texture,roughness:i===4?.5:.81,metalness:i===4?.3:.04}));mesh.rotation.x=-Math.PI/2;mesh.position.y=.795;mesh.receiveShadow=false;mesh.userData.region=i;lift.add(mesh);
  if(i===2){frame.color.setHex(0x6baac7);frame.map=null;frame.metalness=.3;frame.roughness=.18;mesh.material.roughness=.25;mesh.material.metalness=.25;}
  const boardObjects=new Set();lift.traverse(o=>{if(o.isMesh)boardObjects.add(o);});if(!replaceDomain(a,p,i))buildSettlement(a,p,i,originals[i]);enrichDomain(a,p,i);
  for(const x of [-4.9,4.9])for(const z of [-4.9,4.9]){a.cylinder(p,.3,.95,[x,.6,z],i===2?domainMaterials(a).ice:trim);a.cylinder(p,.43,.12,[x,1.03,z],trim);}a.makeNameplate(p,i);const nameplate=p.children.at(-1);const [nameX,nameZ]=plaqueOffset(i);nameplate.position.set(nameX,-.20,nameZ);
  const parts=planConstruction(p,lift,a);
  const glowCanvas=document.createElement('canvas');glowCanvas.width=glowCanvas.height=128;const gx=glowCanvas.getContext('2d'),grad=gx.createRadialGradient(64,64,28,64,64,64);grad.addColorStop(0,'#ffe4a580');grad.addColorStop(.6,'#ffe4a566');grad.addColorStop(1,'#ffe4a500');gx.fillStyle=grad;gx.fillRect(0,0,128,128);const glow=new T.Mesh(new T.PlaneGeometry(18,18),new T.MeshBasicMaterial({map:new T.CanvasTexture(glowCanvas),transparent:true,opacity:0,depthWrite:false,blending:T.AdditiveBlending}));glow.rotation.x=-Math.PI/2;glow.position.y=.18;glow.visible=false;p.add(glow);mesh.material.emissiveMap=texture;
  a.boards.push({canvas,texture,mesh,n,content:p,parts,theme,glow,lift});
 });
 a.hitMeshes=a.disks;
}
function buildSettlement(a,p,i,original){
 if(i===7){greatWall(a,p);return;}
 const M=a.materials;let houseIndex=0;
 function windows(g,w,h,z,columns=3){for(let f=0;f<Math.ceil(h/1.25);f++)for(let j=0;j<columns;j++){const x=(j-(columns-1)/2)*w/(columns+1),y=.65+f*1.14;if(y>h-.2)continue;a.box(g,[.37,.63,.10],[x,y,z],M.paper);a.box(g,[.27,.5,.025],[x,y,z+.065],M.dark);a.box(g,[.023,.5,.025],[x,y,z+.09],M.brass);a.box(g,[.28,.022,.025],[x,y,z+.09],M.brass);}}
 function house(x,z,w=2,h=1.6,chinese=false){const variants=[[],['pavilion','market'],['windmill','greenhouse'],['clocktower','pavilion'],['clocktower','gatehouse','market','well','greenhouse','market','pavilion','well'],['observatory','greenhouse','clocktower','pavilion'],[],['observatory','pavilion','greenhouse','clocktower','pavilion']][i],type=variants[houseIndex++];if(type)return landmark(a,p,type,x,z,type==='windmill'?.82:.95);const g=new T.Group();p.add(g);g.position.set(x,.14,z);a.box(g,[w+.32,.18,2.1],[0,.12,0],M.stone);a.box(g,[w,h,1.8],[0,h/2+.2,0],chinese?M.paper:M.stone);windows(g,w,h,.93,Math.max(2,Math.floor(w)));for(const sign of [-1,1]){const roof=a.box(g,[w*.65,.12,2.35],[sign*w*.26,h+.51,0],chinese?M.jade:M.dark);roof.rotation.z=-sign*.45;for(let k=-6;k<=6;k++)a.rod(g,[0,h+.77,k*.18],[sign*w*.6,h+.25,k*.18],.022,M.brass);}for(const x of [-w*.45,w*.45])a.box(g,[.085,h,.10],[x,h/2+.2,.96],M.wood);a.box(g,[w,.07,.11],[0,h+.14,.96],M.wood);return g;}
 function tower(x,z,h,spire=true){const g=new T.Group();g.position.set(x,.15,z);p.add(g);a.cylinder(g,.93,.2,[0,.13,0],M.stone);a.cylinder(g,.77,h,[0,h/2+.25,0],M.stone);for(let y=1;y<h;y+=1.1){a.torus(g,.80,.045,[0,y,0],M.paper);for(const side of [-1,1])a.box(g,[.22,.53,.05],[side*.25,y-.13,.744],M.dark);}a.cylinder(g,.96,.2,[0,h+.33,0],M.paper);if(spire){a.mesh(g,new T.ConeGeometry(1.05,1.7,8),M.jade,[0,h+1.27,0]);a.rod(g,[0,h+2.12,0],[0,h+2.65,0],.04,M.gold);}else for(let k=0;k<8;k++){const q=k*Math.PI/4;a.box(g,[.23,.42,.23],[Math.sin(q)*.83,h+.63,Math.cos(q)*.83],M.stone);}return g;}
 function arcade(z,span,count){for(let k=0;k<count;k++){const x=-span/2+k*span/(count-1);a.cylinder(p,.15,1.85,[x,1.18,z],M.paper);a.box(p,[.48,.13,.5],[x,.28,z],M.stone);a.box(p,[.40,.13,.42],[x,2.14,z],M.brass);}a.box(p,[span+.55,.23,.65],[0,2.32,z],M.stone);for(let k=0;k<count-1;k++){const x=-span/2+(k+.5)*span/(count-1);const arch=new T.Mesh(new T.TorusGeometry(span/(count-1)*.45,.08,5,16,Math.PI),M.paper);arch.position.set(x,1.6,z);p.add(arch);}}
 function tree(x,z,h=1.8){a.cylinder(p,.10,h,[x,h/2+.2,z],M.wood);a.mesh(p,new T.IcosahedronGeometry(.72,1),M.jade,[x,h+.2,z]);}
 if(i===0){arcade(-8,4.2,3);for(const x of [-8,8]){a.cylinder(p,.2,1.25,[x,.8,-5],M.stone);a.mesh(p,new T.SphereGeometry(.3,10,8),M.gold,[x,1.53,-5]);}tree(-8,5);tree(8,5);}
 if(i===1){if(original){original.position.set(0,.15,-8);original.scale.setScalar(.32);p.add(original);}house(-7.8,-5,2,1.5,true);house(7.8,-5,2,1.5,true);for(const x of [-8,8])tree(x,3);}
 if(i===2){original.position.set(0,.16,-8);original.scale.setScalar(.9);p.add(original);house(-7.9,-5,2.3,1.8);house(7.9,-5,2.3,1.8);for(const x of [-8,8])for(const z of [1,5])tree(x,z,1.7);arcade(-8.1,7.5,6);}
 if(i===3){original.position.set(0,.15,-8);original.scale.setScalar(.55);p.add(original);for(const x of [-8,8]){house(x,-4,2,1.9);tower(x,2,2.4);tree(x,6);} }
 if(i===4){arcade(-8,13,9);house(-7,-8,2.7,3);house(7,-8,2.7,3);for(const x of [-8,8])for(const z of [-3,2,6])house(x,z,2.2,1.5+(z===2?.65:0));const dial=new T.Group();p.add(dial);dial.position.set(0,2.58,-8);a.gear(dial,.7,20,[0,0,0],.15);}
 if(i===5){tower(0,-8,5.2);for(const x of [-7.7,7.7]){tower(x,-7.7,3.4);house(x,-2.4,2.3,2.5);house(x,2,2.1,2);tree(x,6.5);}arcade(-8,11,8);}
 if(i===6){for(const x of [-8,8])for(const z of [-8,-2,5.8])tower(x,z,z===-8?4.3:2.8,false);for(const x of [-8,8]){a.box(p,[.5,1.7,12],[x,1,-.7],M.stone);for(let z=-6;z<5;z+=.65)a.box(p,[.6,.33,.32],[x,2.03,z],M.paper);}a.box(p,[13,1.5,.5],[0,.92,-8],M.stone);house(0,-8,4.7,3.3);for(const x of [-4,4])tower(x,-8,3.4);}
 if(i===7){greatWall(a,p);landmark(a,p,'pavilion',-8.4,1.8,1.05);landmark(a,p,'pavilion',8.4,1.8,1.05);landmark(a,p,'observatory',-8,6.7,.85);landmark(a,p,'greenhouse',8,6.7,.95);for(const x of [-7,7])tree(x,-3.4,1.8);}
 // A low public monument complements the residential, sacred and civic buildings.
 const centerpiece=['well','fountain','fountain','well','fountain','observatory','gatehouse','fountain'][i];landmark(a,p,centerpiece,0,9.15,i===5?.58:i===6?.68:.72);
 if(i===0){landmark(a,p,'market',-8,0,.8);landmark(a,p,'pavilion',8,0,.8);}
 if(i===1)landmark(a,p,'obelisk',-5,-9.3,.65);
 if(i>=6){landmark(a,p,'market',-4.5,8.2,.7);landmark(a,p,'well',4.5,8.2,.7);}
 // Lanterns and bracketed exposed clockwork sit outside the playable square.
 for(const x of [-6.65,6.65])for(const z of [-6.65,6.65]){a.box(p,[.28,.18,.28],[x,.25,z],M.stone);a.cylinder(p,.045,.60,[x,.63,z],M.brass);a.box(p,[.20,.25,.20],[x,1.03,z],M.paper);a.mesh(p,new T.ConeGeometry(.2,.17,4),M.dark,[x,1.24,z]);}
 if(i>1){a.box(p,[1.6,.13,1.6],[-8,.25,8.2],M.dark);a.cylinder(p,.13,.25,[-8,.40,8.2]);a.gear(p,.61,18,[-8,.57,8.2],.13);}
}
export function paintBoard(a,index,state){
 if(index===7){const progress=syncWallBeacons(a.wallBeacons,state.values);if(a.canvas&&progress){a.canvas.dataset.beaconsLit=String(progress.wallLit);a.canvas.dataset.beaconsTotal='8';}}
 const b=a.boards[index],{n,canvas,texture}=b,x=canvas.getContext('2d'),step=(SIZE-PAD*2)/(n+1),values=state.values;
 const theme=b.theme;x.fillStyle=theme.paper;x.fillRect(0,0,SIZE,SIZE);
 for(let k=0;k<500;k++){x.strokeStyle=k%2?'#c3a26908':'#10090516';const y=(k*37)%SIZE;x.beginPath();x.moveTo(0,y);const wave=index===1||index===2?80:4;x.bezierCurveTo(360,y-wave*Math.sin(k),800,y+wave,SIZE,y);x.stroke();}
 if(index===1){const wash=x.createRadialGradient(SIZE*.45,SIZE*.40,80,SIZE*.5,SIZE*.5,SIZE*.8);wash.addColorStop(0,'#f7f3e7');wash.addColorStop(1,'#e9e0c9');x.fillStyle=wash;x.fillRect(0,0,SIZE,SIZE);for(let k=0;k<6500;k++){const px=(k*173.317)%SIZE,py=(k*257.713)%SIZE;x.strokeStyle=k%3?'#8b7d4e0b':'#ffffff33';x.lineWidth=k%5===0?.65:.3;x.beginPath();x.moveTo(px,py);x.lineTo(px+2+(k%7)*1.2,py+((k%5)-2)*.4);x.stroke();}}
 if(index===2){x.strokeStyle='#effaff88';x.lineWidth=1.3;for(let j=0;j<15;j++){const px=(j*173)%SIZE,py=(j*257)%SIZE;x.beginPath();x.moveTo(px,py);x.lineTo(px+53,py+81);x.lineTo(px+30,py+131);x.stroke();}}
 if(index===5){for(let k=0;k<90;k++){const px=(k*167)%SIZE,py=(k*233)%SIZE;x.fillStyle='#d2d9ee28';x.fillRect(px,py,1.6,1.6);}}
 x.strokeStyle=theme.line;x.lineWidth=2;for(const inset of [12,22])x.strokeRect(inset,inset,SIZE-inset*2,SIZE-inset*2);
 const cell=(r,c)=>[PAD+(c+1)*step,PAD+(r+1)*step];
 x.textAlign='center';x.textBaseline='middle';x.font=`${step*.43}px Atlas,Georgia,serif`;
 for(let j=0;j<n;j++){x.fillStyle=state.skill==='identity'&&j===n-1?'#f18777':theme.ink;x.fillText(j+1,PAD+(j+1.5)*step,PAD+step*.5);x.fillText(j+1,PAD+step*.5,PAD+(j+1.5)*step);}
 for(let r=0;r<n;r++)for(let c=0;c<n;c++){const k=r*n+c,[px,py]=cell(r,c),classes=state.cells?.[k]?.classes||'';x.lineWidth=index===1?2.7:1.6;x.strokeStyle=theme.line;x.strokeRect(px,py,step,step);const accent=classes.includes('error-mark')?'#f18777':classes.includes('path-mark')?'#e3c276':classes.includes('cancel-mark')?'#84c4ab':null;if(k===state.selected||accent){x.strokeStyle=accent||(index===1?'#7e6950':index===2?'#58442b':'#efd095');x.lineWidth=k===state.selected?3.5:2;x.strokeRect(px+4,py+4,step-8,step-8);}
 x.fillStyle=classes.includes('identity-mark')?'#f18777':classes.includes('inverse-mark')?'#baa0e7':accent||(classes.includes('given')?theme.given:theme.ink);const fixed=classes.includes('given');x.font=`${fixed?'700':'italic 400'} ${step*(fixed?.57:.61)}px ${fixed?'Atlas,Georgia':'Georgia'},serif`;if(values[k]){if(fixed&&index!==1){x.lineWidth=1.8;x.strokeStyle=index===2?'#332a2070':'#100c08a0';x.strokeText(values[k],px+step/2,py+step*.52+1.7);x.shadowColor=index===2?'#fff8':'#000';x.shadowOffsetY=1;x.shadowBlur=1;}else if(!fixed&&!classes.includes('identity-mark')&&!classes.includes('inverse-mark')&&!accent)x.fillStyle=index===1?'#43574d':index===2?'#305566':'#c1e0e8';x.fillText(values[k],px+step/2,py+step*.52);x.shadowOffsetY=0;x.shadowBlur=0;if(fixed&&index!==1){x.strokeStyle=index===2?'#514b3e55':'#e2d2a34a';x.lineWidth=1;x.beginPath();x.moveTo(px+step*.34,py+step*.83);x.lineTo(px+step*.66,py+step*.83);x.stroke();}}else{x.fillStyle='#8d785555';x.beginPath();x.arc(px+step/2,py+step/2,2.2,0,Math.PI*2);x.fill();}}
 texture.needsUpdate=true;
}
export function cellPoint(a,index,k){const n=index+2,step=(SIZE-PAD*2)/(n+1),px=PAD+(k%n+1.5)*step,py=PAD+(Math.floor(k/n)+1.5)*step;return a.boards[index].lift.localToWorld(new T.Vector3((px/SIZE-.5)*WIDTH,.805,(py/SIZE-.5)*WIDTH));}
