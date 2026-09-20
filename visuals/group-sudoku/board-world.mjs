import * as T from '../3d/vendor/three.module.js';
const WIDTH=10.8,SIZE=1152,PAD=44;
// Every playable cell is drawn on the same horizontal mesh as the timber board.
// Hit targets are projected from these world coordinates, so orbiting never detaches input.
export function installBoards(a){
 const originals=[null,a.pagoda,a.manor,a.cathedral,a.crystal,a.ai,null,null];
 originals.forEach(g=>g?.removeFromParent());
 a.boards=[];
 a.platforms.forEach((p,i)=>{
  p.clear();const n=i+2,M=a.materials;
  a.box(p,[21,.65,21],[0,-.48,0],M.dark);a.box(p,[20.65,.16,20.65],[0,-.08,0],M.brass);a.box(p,[20.35,.12,20.35],[0,.05,0],M.paving);
  // Broad clear central court; buildings never occupy the board footprint.
  a.box(p,[11.8,.52,11.8],[0,.40,0],M.wood);a.box(p,[11.5,.065,11.5],[0,.69,0],M.brass);a.box(p,[11.36,.07,11.36],[0,.75,0],M.wood);
  for(const x of [-5.73,5.73])for(const z of [-5.73,5.73])a.cylinder(p,.06,.035,[x,.69,z],M.gold);
  const canvas=document.createElement('canvas');canvas.width=canvas.height=SIZE;const texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;texture.anisotropy=Math.min(8,a.renderer.capabilities.getMaxAnisotropy());
  const mesh=new T.Mesh(new T.PlaneGeometry(WIDTH,WIDTH),new T.MeshStandardMaterial({map:texture,roughness:.81,metalness:.04}));mesh.rotation.x=-Math.PI/2;mesh.position.y=.795;mesh.receiveShadow=false;mesh.userData.region=i;p.add(mesh);
  a.boards.push({canvas,texture,mesh,n});
  // Engraved perimeter trim and alternating masonry joints.
  for(const z of [-10,10])a.box(p,[20,.045,.065],[0,.14,z],M.gold);
  for(const x of [-10,10])a.box(p,[.065,.045,20],[x,.14,0],M.gold);
  for(let k=0;k<20;k++)for(const side of [-1,1])a.box(p,[.45,.04,.06],[-9.5+k,.15,side*9.8],M.brass);
  const ring=a.torus(p,10.4,.055,[0,-.15,0],M.gold.clone());a.markers[i]=ring;
  buildSettlement(a,p,i,originals[i]);
  a.makeNameplate(p,i);const plaque=p.children.at(-1);plaque.position.set(0,.23,10);
 });
 a.hitMeshes=a.boards.map(b=>b.mesh);
}
function buildSettlement(a,p,i,original){
 const M=a.materials;
 function windows(g,w,h,z,columns=3){for(let f=0;f<Math.ceil(h/1.25);f++)for(let j=0;j<columns;j++){const x=(j-(columns-1)/2)*w/(columns+1),y=.65+f*1.14;if(y>h-.2)continue;a.box(g,[.37,.63,.10],[x,y,z],M.paper);a.box(g,[.27,.5,.025],[x,y,z+.065],M.dark);a.box(g,[.023,.5,.025],[x,y,z+.09],M.brass);a.box(g,[.28,.022,.025],[x,y,z+.09],M.brass);}}
 function house(x,z,w=2,h=1.6,chinese=false){const g=new T.Group();p.add(g);g.position.set(x,.14,z);a.box(g,[w+.32,.18,2.1],[0,.12,0],M.stone);a.box(g,[w,h,1.8],[0,h/2+.2,0],chinese?M.paper:M.stone);windows(g,w,h,.93,Math.max(2,Math.floor(w)));for(const sign of [-1,1]){const roof=a.box(g,[w*.65,.12,2.35],[sign*w*.26,h+.51,0],chinese?M.jade:M.dark);roof.rotation.z=-sign*.45;for(let k=-6;k<=6;k++)a.rod(g,[0,h+.77,k*.18],[sign*w*.6,h+.25,k*.18],.022,M.brass);}for(const x of [-w*.45,w*.45])a.box(g,[.085,h,.10],[x,h/2+.2,.96],M.wood);a.box(g,[w,.07,.11],[0,h+.14,.96],M.wood);return g;}
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
 if(i===7){house(0,-8,5,4.2,true);for(const x of [-7.8,7.8]){tower(x,-8,5);house(x,-3,2.5,3.1,true);tower(x,2.2,3.8);house(x,6.6,2.4,2,true);}arcade(-6.8,10,10);for(const x of [-4.5,4.5]){tower(x,-8,3.5);a.rod(p,[x,4,-8],[0,5.6,-8],.06,M.gold);}}
 // Lanterns and bracketed exposed clockwork sit outside the playable square.
 for(const x of [-6.65,6.65])for(const z of [-6.65,6.65]){a.box(p,[.28,.18,.28],[x,.25,z],M.stone);a.cylinder(p,.045,.60,[x,.63,z],M.brass);a.box(p,[.20,.25,.20],[x,1.03,z],M.paper);a.mesh(p,new T.ConeGeometry(.2,.17,4),M.dark,[x,1.24,z]);}
 if(i>1){a.box(p,[1.6,.13,1.6],[-8,.25,8.2],M.dark);a.cylinder(p,.13,.25,[-8,.40,8.2]);a.gear(p,.61,18,[-8,.57,8.2],.13);}
}
export function paintBoard(a,index,state){
 const b=a.boards[index],{n,canvas,texture}=b,x=canvas.getContext('2d'),step=(SIZE-PAD*2)/(n+1),values=state.values;
 x.fillStyle='#30271d';x.fillRect(0,0,SIZE,SIZE);
 for(let k=0;k<1000;k++){x.strokeStyle=k%2?'#c3a26905':'#10090520';const y=(k*37)%SIZE;x.beginPath();x.moveTo(0,y);x.bezierCurveTo(360,y-5,800,y+5,SIZE,y);x.stroke();}
 const cell=(r,c)=>[PAD+(c+1)*step,PAD+(r+1)*step];
 x.textAlign='center';x.textBaseline='middle';x.font=`${step*.43}px Atlas,Georgia,serif`;
 for(let j=0;j<n;j++){x.fillStyle=state.skill==='identity'&&j===n-1?'#f18777':'#c5a365';x.fillText(j+1,PAD+(j+1.5)*step,PAD+step*.5);x.fillText(j+1,PAD+step*.5,PAD+(j+1.5)*step);}
 for(let r=0;r<n;r++)for(let c=0;c<n;c++){const k=r*n+c,[px,py]=cell(r,c),classes=state.cells?.[k]?.classes||'';x.lineWidth=1.6;x.strokeStyle='#b493555e';x.strokeRect(px,py,step,step);const accent=classes.includes('error-mark')?'#f18777':classes.includes('path-mark')?'#e3c276':classes.includes('cancel-mark')?'#84c4ab':null;if(k===state.selected||accent){x.strokeStyle=accent||'#efd095';x.lineWidth=k===state.selected?3.5:2;x.strokeRect(px+4,py+4,step-8,step-8);}
 x.fillStyle=classes.includes('identity-mark')?'#f18777':classes.includes('inverse-mark')?'#baa0e7':accent||(classes.includes('given')?'#bda781':'#f6e8c4');x.font=`${step*.59}px Atlas,Georgia,serif`;if(values[k]){x.shadowColor='#000';x.shadowOffsetY=2;x.shadowBlur=1;x.fillText(values[k],px+step/2,py+step*.52);x.shadowOffsetY=0;x.shadowBlur=0;}else{x.fillStyle='#8d785555';x.beginPath();x.arc(px+step/2,py+step/2,2.2,0,Math.PI*2);x.fill();}}
 texture.needsUpdate=true;
}
export function cellPoint(a,index,k){const n=index+2,step=(SIZE-PAD*2)/(n+1),px=PAD+(k%n+1.5)*step,py=PAD+(Math.floor(k/n)+1.5)*step;return a.platforms[index].localToWorld(new T.Vector3((px/SIZE-.5)*WIDTH,.805,(py/SIZE-.5)*WIDTH));}
