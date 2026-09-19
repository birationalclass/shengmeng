import * as THREE from 'three';
import {RoundedBoxGeometry} from './vendor/geometries/RoundedBoxGeometry.js';
import {Water} from './vendor/objects/Water.js';
import {Sky} from './vendor/objects/Sky.js';

export async function createRetreat(renderer,scene,report){
  let seed=82573;
  const random=()=>{seed=(seed*1664525+1013904223)>>>0;return seed/4294967296;};
  const loader=new THREE.TextureLoader();
  async function texture(name,repeat=1,srgb=false){
    const map=await loader.loadAsync('./assets/'+name);map.wrapS=map.wrapT=THREE.RepeatWrapping;
    map.repeat.set(repeat,repeat);map.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());
    if(srgb)map.colorSpace=THREE.SRGBColorSpace;return map;
  }
  report('正在铺设材质与水面…');
  const [woodMap,woodNormal,woodRough,waterNormal,stoneMap,stoneNormal,stoneRough]=await Promise.all([
    texture('wood-color.jpg',5,true),texture('wood-normal.jpg',5),texture('wood-rough.jpg',5),texture('waternormals.jpg',1),
    texture('stone-color.jpg',4,true),texture('stone-normal.jpg',4),texture('stone-rough.jpg',4)
  ]);
  const mat=(color,roughness=.7,metalness=0,other={})=>new THREE.MeshStandardMaterial({color,roughness,metalness,...other});
  const steel=mat('#1d2526',.27,.82),stone=mat('#787e74',.55,0,{map:stoneMap,normalMap:stoneNormal,roughnessMap:stoneRough,normalScale:new THREE.Vector2(.12,.12)}),edge=mat('#111f20',.31,.25);
  const brass=mat('#c7a779',.25,.78),timber=mat('#796143',.68,0,{map:woodMap,normalMap:woodNormal,normalScale:new THREE.Vector2(.2,.2),roughnessMap:woodRough});
  const pale=mat('#c3b59d',.92),darkFabric=mat('#465955',.98),soil=mat('#302d21',1),leaf=mat('#46734e',.9,0,{side:THREE.DoubleSide});
  const glass=new THREE.MeshPhysicalMaterial({color:'#c3e7dc',roughness:.07,metalness:.05,transparent:true,opacity:.15,depthWrite:false,side:THREE.DoubleSide});
  const light=mat('#ffe2ac',.5,0,{emissive:'#ffcb79',emissiveIntensity:2.3});
  const blackboard=mat('#153f38',.95),ink=mat('#dddcc5',1);
  const materials={steel,stone,edge,brass,timber,pale,darkFabric,soil,leaf,glass,light,blackboard,ink};
  const boxes=new THREE.BoxGeometry(1,1,1),round=new RoundedBoxGeometry(1,1,1,3,.13);
  const cylinder=new THREE.CylinderGeometry(1,1,1,12),sphere=new THREE.IcosahedronGeometry(1,1);
  const batches=new Map(),dummy=new THREE.Object3D();
  function instance(geo,material,p,s,r=[0,0,0]){
    const key=geo.uuid+material.uuid;if(!batches.has(key))batches.set(key,{geo,material,matrices:[]});
    dummy.position.fromArray(p);dummy.scale.fromArray(s);dummy.rotation.set(...r);dummy.updateMatrix();
    batches.get(key).matrices.push(dummy.matrix.clone());
  }
  const box=(p,s,m=stone,r)=>instance(boxes,m,p,s,r);
  const soft=(p,s,m=pale,r)=>instance(round,m,p,s,r);
  function beam(a,b,radius,material=steel){
    const av=new THREE.Vector3(...a),bv=new THREE.Vector3(...b),mid=av.clone().add(bv).multiplyScalar(.5),direction=bv.clone().sub(av);
    const q=new THREE.Quaternion().setFromUnitVectors(new THREE.Vector3(0,1,0),direction.clone().normalize());
    const rot=new THREE.Euler().setFromQuaternion(q);instance(cylinder,material,mid.toArray(),[radius,direction.length(),radius],[rot.x,rot.y,rot.z]);
  }
  function litStrip(p,size){box(p,size,light);}
  function floor(y,w,d,cx=0,cz=0){
    box([cx,y,cz],[w,.4,d],edge);box([cx,y+.23,cz],[w-.16,.09,d-.16],stone);
    litStrip([cx,y-.06,cz+d/2+.01],[w-.3,.035,.025]);
    litStrip([cx+w/2+.01,y-.06,cz],[.025,.035,d-.3]);
  }
  function glazing(x,y,z,width,height,axis='x'){
    const s=axis==='x'?[width,height,.035]:[.035,height,width];
    box([x,y+height/2,z],s,glass);
    const n=Math.ceil(width/2);
    for(let i=0;i<=n;i++){
      const k=(i/n-.5)*width;box([x+(axis==='x'?k:0),y+height/2,z+(axis==='x'?0:k)],[.075,height,.075],steel);
    }
    for(const h of [0,height])box([x,y+h,z],axis==='x'?[width,.09,.11]:[.11,.09,width],steel);
  }
  function railing(x,y,z,w,axis='x'){
    glazing(x,y,z,w,1.05,axis);
    box([x,y+1.08,z],axis==='x'?[w,.045,.05]:[.05,.045,w],brass);
  }
  function planter(x,y,z,w=2){
    box([x,y+.24,z],[w,.48,.9],edge);box([x,y+.48,z],[w-.13,.03,.75],soil);
    for(let i=0;i<Math.floor(w*7);i++){
      const px=x+(random()-.5)*(w-.1),pz=z+(random()-.5)*.7;
      instance(sphere,leaf,[px,y+.55+random()*.24,pz],[.15+random()*.18,.25+random()*.25,.15+random()*.15]);
    }
  }
  function tree(x,y,z,scale=1){
    const h=3.6*scale;
    beam([x,y,z],[x+.13*scale,y+h,z],.065*scale,timber);
    for(let b=0;b<7;b++){
      const angle=b*2.399,by=y+h*(.56+random()*.4),length=(.7+random()*.7)*scale;
      const end=[x+Math.cos(angle)*length,by+.45*scale,z+Math.sin(angle)*length];
      beam([x,by-.55*scale,z],end,.025*scale,timber);
      for(let j=0;j<15;j++){
        const a=random()*Math.PI*2,r=Math.sqrt(random())*.7*scale;
        instance(sphere,leaf,[end[0]+Math.cos(a)*r,end[1]+(random()-.5)*.45*scale,end[2]+Math.sin(a)*r],[.24*scale,.11*scale,.32*scale],[random(),random()*6,random()]);
      }
    }
  }
  function sofa(x,y,z,angle=0){
    const group=new THREE.Group();group.position.set(x,y,z);group.rotation.y=angle;
    // Transform upholstered modules into the common instancing batches.
    const part=(p,s,m)=>{const v=new THREE.Vector3(...p).applyAxisAngle(new THREE.Vector3(0,1,0),angle).add(group.position);soft(v.toArray(),s,m,[0,angle,0]);};
    part([0,.21,0],[3.1,.34,1.1],edge);part([0,.56,-.48],[3.05,.85,.27],darkFabric);
    for(const a of [-1,0,1]){part([a,.46,.04],[.96,.22,.91],pale);part([a,.73,-.25],[.86,.56,.23],pale);}
    part([-1.52,.52,0],[.22,.55,1.1],darkFabric);part([1.52,.52,0],[.22,.55,1.1],darkFabric);
    for(const px of [-1.2,1.2])for(const pz of [-.35,.35])part([px,.06,pz],[.09,.15,.09],brass);
  }
  function table(x,y,z,w=2,d=1){
    soft([x,y+.57,z],[w,.12,d],timber);
    for(const dx of [-w*.36,w*.36])for(const dz of [-d*.33,d*.33])box([x+dx,y+.28,z+dz],[.075,.55,.075],brass);
    // Closed notebooks and ceramic bowl.
    box([x-.2,y+.66,z],[.4,.055,.3],blackboard);
    instance(cylinder,pale,[x+.4,y+.72,z],[.13,.19,.13]);
  }
  report('正在搭建书院与庭院…');
  floor(0,33,29,0,0);floor(5.15,27,20,-1,-1);floor(9.8,19,14,-4,-3);floor(13.6,13,10,-5,-3);
  for(const y of [.28,5.43,10.08]){
    const upper=y>9,mid=y>5,w=upper?11:mid?18:22,d=upper?8:mid?12:14,cx=upper?-5:mid?-3:0,cz=-3;
    const h=upper?3.52:mid?4.37:4.87;
    box([cx,y+.01,cz],[w,.035,d],timber);
    glazing(cx-w/2,y,cz,d,h,'z');
    if(!mid){
      // A real opening to the meeting wing; do not leave glass across the link.
      glazing(cx+w/2,y,-4.8,10.4,h,'z');glazing(cx+w/2,y,3.6,.8,h,'z');
    }else glazing(cx+w/2,y,cz,d,h,'z');
    glazing(cx,y,cz-d/2,w,h);
    // Entrance at ground front; upper fronts are deliberately open loggias.
    if(!mid){glazing(cx-6.5,y,cz+d/2,9,h);glazing(cx+6.5,y,cz+d/2,9,h);}
    for(const x of [-w/2,w/2])for(const z of [-d/2,d/2])box([cx+x,y+h/2,cz+z],[.19,h,.19],steel);
    for(let x=-w/2;x<=w/2;x+=.48)box([cx+x,y+h-.18,cz],[.12,.16,d],timber);
    for(const z of [-d/2+.5,d/2-.5])litStrip([cx,y+h-.28,cz+z],[w-.6,.04,.05]);
  }
  // Vertical fins give the facade real thickness and depth at glancing angles.
  for(let z=-9;z<=3;z+=.63)box([-11.2,5,z],[.25,10,.14],timber);
  railing(-1,5.43,8.8,27);railing(12.4,5.43,-1,19.5,'z');railing(-14.4,5.43,-1,19.5,'z');
  railing(-4,10.08,3.9,19);railing(5.4,10.08,-3,13.7,'z');
  for(let i=0;i<11;i++){const y=-1.65+i*.18;box([-6,y,16-i*.37],[6,.18,.55],stone);litStrip([-6,y+.095,16-i*.37+.26],[5.8,.022,.025]);}
  // Open stair between levels, to the west of the main reading room.
  for(let i=0;i<26;i++){box([-12.5,.4+i*.19,3-i*.38],[2.05,.16,.43],timber);}
  beam([-13.6,.9,3.2],[-13.6,5.8,-6.6],.035,brass);
  for(let i=0;i<12;i++)beam([-13.6,.5+i*.42,3-i*.85],[-13.6,1.4+i*.42,3-i*.85],.02,steel);
  // Reflection pool and stone footbridge (not a backdrop image).
  box([8,.18,8],[11,.4,9],edge);box([8,.4,8],[10.7,.03,8.7],mat('#164d4a',.27,.4));
  const water=new Water(new THREE.PlaneGeometry(10.55,8.55),{
    textureWidth:1024,textureHeight:1024,waterNormals:waterNormal,sunDirection:new THREE.Vector3(-.5,.5,-.5),
    sunColor:0xffe8ca,waterColor:0x164c48,distortionScale:1.5,alpha:1,fog:true
  });
  water.rotation.x=-Math.PI/2;water.position.set(8,.49,8);scene.add(water);
  for(let i=0;i<8;i++){const x=5.2+i*.56,z=4.4+i*.99;box([x,.56,z],[1.5,.13,.68],stone);litStrip([x,.49,z+.34],[1.45,.025,.035]);}
  for(const z of [3.5,12.5])box([8,.46,z],[11.1,.12,.23],stone);
  for(const x of [2.5,13.5])box([x,.46,8],[.23,.12,9],stone);
  // Exterior furniture and planted edges.
  sofa(-7,.3,7);sofa(-11,.3,9,Math.PI/2);table(-7,.3,9,2.2,1.2);
  sofa(-4,5.45,6);table(-4,5.45,7.4,2.1,.85);
  for(const y of [.28,5.43])for(let x=-12;x<=11;x+=3)planter(x,y,y<1?-12:8.3,2.4);
  for(const p of [[-13,.3,2],[-12,.3,11],[14,.3,-10],[-11,5.43,5],[9,5.43,-8],[-10,10.08,2]]){
    planter(...p,1.6);tree(p[0],p[1]+.5,p[2],.75);
  }
  // Tall shelving with hundreds of individual books, timber ends and brass rails.
  const bookMats=['#3f6860','#8e7251','#baa98a','#474d50','#6e554e'].map(c=>mat(c,.9));
  for(const x of [-7,-3,1,5]){
    box([x,2.6,-9.65],[3.6,4.6,.45],edge);
    for(let row=0;row<6;row++){
      const y=.65+row*.67;box([x,y,-9.2],[3.5,.075,.62],timber);
      for(let b=0;b<20;b++){
        const h=.34+random()*.21,bx=x-1.56+b*.163;
        box([bx,y+h/2+.05,-9.12],[.12,h,.36],bookMats[Math.floor(random()*bookMats.length)]);
        box([bx,y+h*.7,-8.93],[.08,.012,.009],brass);
      }
      litStrip([x,y+.025,-8.92],[3.3,.025,.018]);
    }
  }
  sofa(3,.31,-5,Math.PI);sofa(7,.31,-2,-Math.PI/2);table(3,.31,-2,2.6,1.3);
  sofa(-6,5.45,-2);table(-6,5.45,0,2.4,1);
  for(const x of [-7,-3,1]){table(x,10.1,-4,2.6,1.3);sofa(x,10.1,-6);}
  // A second, offset building volume: enclosed seminar hall, upper discussion
  // pavilion, connecting gallery and a cantilevered ocean-facing belvedere.
  report('正在扩建海景会议翼…');
  floor(0,20,20,28,-1);floor(5.15,23,22,28,-1);
  floor(0,10,3.2,15.5,1.8);floor(3.6,10,3.6,15.5,1.8);
  glazing(15.5,.28,.2,10,3.25);glazing(15.5,.28,3.4,10,3.25);
  box([28,.29,-1],[19.8,.04,19.8],timber);
  // Doorway on the west connects the hall to the gallery without a glass barrier.
  glazing(18,.28,-5.4,11.2,4.87,'z');glazing(18,.28,6.2,5.6,4.87,'z');
  glazing(28,.28,-11,20,4.87);glazing(28,.28,9,20,4.87);
  // Three broad ocean-view panes and a walk-through opening near the south end.
  glazing(38,.28,-2.8,16.4,4.87,'z');glazing(38,.28,8.4,1.2,4.87,'z');
  for(const x of [18,38])for(const z of [-11,9])box([x,2.7,z],[.23,4.9,.23],steel);
  for(let x=19;x<38;x+=.65)box([x,4.92,-1],[.13,.17,19.8],timber);
  for(const z of [-9.8,7.8])litStrip([28,4.77,z],[18,.045,.045]);
  // Full-height structural piers and a visible cliff plinth support the extension.
  box([28,-1.2,-1],[19.6,2,19.6],stone);
  for(const z of [-10,0,8])box([37,-4.3,z],[.85,8.1,.85],stone);
  floor(0,11,26,43.5,-1);
  railing(49,.28,-1,26,'z');railing(43.5,.28,12,11);railing(43.5,.28,-14,11);
  for(const z of [-11,-4,3,10])beam([37,-3,z],[47,-.2,z],.13,steel);
  for(const z of [-10,0,9]){sofa(44,.3,z,Math.PI/2);table(46,.3,z,1.1,1.1);}
  for(const z of [-12,11])planter(41,.3,z,3);
  // Fourteen modeled conference chairs surround a single generous oak table.
  soft([28,1.08,-1],[4.6,.18,11.8],timber);
  for(const z of [-4.5,2.5])box([28,.68,z],[2.7,.68,.45],edge);
  const conferenceTable=new THREE.Object3D();conferenceTable.name='Ocean conference table';
  conferenceTable.position.set(28,1.08,-1);conferenceTable.userData={seats:14,room:[20,20]};scene.add(conferenceTable);
  function chair(x,z,angle){
    const part=(p,s,m)=>{const v=new THREE.Vector3(...p).applyAxisAngle(new THREE.Vector3(0,1,0),angle).add(new THREE.Vector3(x,.3,z));soft(v.toArray(),s,m,[0,angle,0]);};
    part([0,.48,0],[.78,.17,.82],darkFabric);part([0,.94,-.36],[.78,.86,.16],pale);
    for(const a of [-.43,.43])part([a,.77,0],[.09,.1,.72],timber);
    for(const a of [-.29,.29])for(const b of [-.28,.28])part([a,.22,b],[.045,.44,.045],steel);
  }
  for(const z of [-5.7,-3.8,-1.9,0,1.9,3.8]){
    chair(24.65,z,Math.PI/2);chair(31.35,z,-Math.PI/2);
    for(const x of [26.25,29.75]){
      box([x,1.21,z],[.52,.025,.7],pale);box([x+.32,1.22,z],[.025,.022,.52],brass);
      instance(cylinder,glass,[x,1.32,z+.52],[.075,.23,.075]);
    }
  }
  chair(28,-8.05,Math.PI);chair(28,6.05,0);
  litStrip([28,4.05,-1],[.16,.1,11]);
  for(const z of [-5,3])beam([28,4.12,z],[28,5,z],.012,steel);
  // A dedicated presentation wall does not obstruct the ocean-facing glazing.
  const seminarCanvas=document.createElement('canvas');seminarCanvas.width=1536;seminarCanvas.height=768;
  const seminarCtx=seminarCanvas.getContext('2d');seminarCtx.fillStyle='#142c2c';seminarCtx.fillRect(0,0,1536,768);
  seminarCtx.fillStyle='#e7d4aa';seminarCtx.textAlign='center';seminarCtx.font='86px "PingFang SC", sans-serif';seminarCtx.fillText('海景会议室',768,245);
  seminarCtx.font='40px "Times New Roman", serif';seminarCtx.fillText('MATHEMATICAL REFUGE / SEMINAR ROOM',768,350);
  seminarCtx.fillStyle='#b6d6c7';seminarCtx.font='48px "PingFang SC", sans-serif';seminarCtx.fillText('让不同的想法，在这里相遇。',768,545);
  const seminarMap=new THREE.CanvasTexture(seminarCanvas);seminarMap.colorSpace=THREE.SRGBColorSpace;
  const seminarScreen=new THREE.Mesh(new THREE.PlaneGeometry(2.6,1.3),new THREE.MeshStandardMaterial({map:seminarMap,roughness:.7}));
  seminarScreen.name='Conference entrance sign';seminarScreen.position.set(17.95,4.35,1.8);seminarScreen.rotation.y=-Math.PI/2;scene.add(seminarScreen);
  // Upper floor set back from the edge: a smaller glazed room plus roof garden.
  floor(9.1,14,11,27,-5);
  box([27,5.45,-5],[13,.035,10],timber);
  glazing(20.5,5.43,-5,10,3.67,'z');glazing(33.5,5.43,-5,10,3.67,'z');
  glazing(27,5.43,-10,13,3.67);glazing(23,5.43,0,5,3.67);glazing(31,5.43,0,5,3.67);
  for(const x of [20.5,33.5])for(const z of [-10,0])box([x,7.25,z],[.16,3.67,.16],steel);
  sofa(24,5.45,-7);sofa(30,5.45,-7);table(27,5.45,-4,3.8,1.5);
  railing(39.5,5.43,-1,22,'z');railing(28,5.43,10,23);railing(28,5.43,-12,23);
  for(const x of [24,30,36]){sofa(x,5.45,3,Math.PI);table(x,5.45,5,1.6,.9);}
  for(const x of [22,28,34])planter(x,5.43,9.25,3);
  // Exterior stair lands at the open west side of the upper terrace.
  floor(0,5,15,17,8);
  for(let i=0;i<27;i++)box([17,.38+i*(5.05/26),13-i*.36],[2,.16,.4],timber);
  beam([15.9,1.3,13.2],[15.9,6.35,3.64],.04,brass);
  beam([18.1,1.3,13.2],[18.1,6.35,3.64],.04,brass);
  for(let i=0;i<14;i++)for(const x of [15.9,18.1])beam([x,.4+i*.385,13-i*.72],[x,1.3+i*.385,13-i*.72],.022,steel);
  // Independent chalkboards, with brief mathematical statements rather than
  // unverified solved/unsolved status announcements.
  function chalkboard(name,x,rotation,draw){
    const canvas=document.createElement('canvas');canvas.width=1536;canvas.height=768;
    const ctx=canvas.getContext('2d');ctx.fillStyle='#173d34';ctx.fillRect(0,0,1536,768);draw(ctx);
    const map=new THREE.CanvasTexture(canvas);map.colorSpace=THREE.SRGBColorSpace;
    map.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());
    const backing=x>0?x+.1:x-.1;
    box([backing,2.6,-3],[.16,3.1,5.8],timber);
    const board=new THREE.Mesh(new THREE.PlaneGeometry(5.5,2.8),new THREE.MeshStandardMaterial({map,roughness:.95}));
    board.name=name;board.rotation.y=rotation;board.position.set(x,2.6,-3);scene.add(board);
  }
  function fracturedNS(ctx){
    // Clip a single complete glyph layer into independently displaced shards.
    // The low-opacity fragments stay behind the readable mathematical text.
    const glyph=document.createElement('canvas');glyph.width=1536;glyph.height=768;
    const g=glyph.getContext('2d');g.fillStyle='#a3c8b2';g.textAlign='center';
    g.font='bold 650px "Times New Roman", serif';g.fillText('NS',768,650);
    const rows=[
      [[50,30],[410,15],[785,45],[1150,20],[1490,40]],
      [[35,295],[460,245],[745,330],[1090,265],[1510,300]],
      [[45,525],[385,550],[830,495],[1175,550],[1495,510]],
      [[30,755],[445,750],[790,755],[1110,750],[1510,745]]
    ];
    for(let r=0;r<3;r++)for(let c=0;c<4;c++){
      const polygon=[rows[r][c],rows[r][c+1],rows[r+1][c+1],rows[r+1][c]];
      const cx=polygon.reduce((sum,p)=>sum+p[0],0)/4,cy=polygon.reduce((sum,p)=>sum+p[1],0)/4;
      const dx=(cx-768)*.024+(r%2?4:-4),dy=(cy-384)*.028;
      ctx.save();ctx.globalAlpha=.23;
      ctx.translate(cx+dx,cy+dy);ctx.rotate(((r*4+c)%3-1)*.012);ctx.translate(-cx,-cy);
      ctx.beginPath();polygon.forEach((p,i)=>{const x=cx+(p[0]-cx)*.947,y=cy+(p[1]-cy)*.947;if(i)ctx.lineTo(x,y);else ctx.moveTo(x,y);});
      ctx.closePath();ctx.clip();ctx.drawImage(glyph,0,0);ctx.restore();
    }
  }
  chalkboard('NS conjecture blackboard',10.72,-Math.PI/2,ctx=>{
    fracturedNS(ctx);
    ctx.fillStyle='#eee7cf';ctx.font='72px "PingFang SC", sans-serif';ctx.fillText('NS 方程 · 存在性与光滑性',85,115);
    ctx.font='64px "Times New Roman", serif';ctx.fillText('∂ₜu + (u · ∇)u = νΔu − ∇p',100,255);ctx.fillText('∇ · u = 0,     u(x, 0) = u₀(x)',100,355);
    ctx.font='42px "PingFang SC", sans-serif';ctx.fillStyle='#b8d3bd';ctx.fillText('三维、无外力、周期边界，ν > 0。',100,470);
    ctx.fillStyle='#eee7cf';ctx.fillText('任意光滑且散度为零的初始速度，',100,565);ctx.fillText('能否产生对所有时间都保持光滑的解？',100,635);
  });
  chalkboard('Hodge conjecture blackboard',-10.72,Math.PI/2,ctx=>{
    ctx.fillStyle='#eee7cf';ctx.font='82px "PingFang SC", sans-serif';ctx.fillText('Hodge 猜想 ？',85,130);
    ctx.font='48px "PingFang SC", sans-serif';ctx.fillText('在光滑复射影簇 X 上，',100,290);
    ctx.fillText('每个有理的 (p, p) 型上同调类，',100,385);
    ctx.fillText('是否都是余维 p 的代数子簇之类',100,480);ctx.fillText('的有理线性组合？',100,565);
    ctx.fillStyle='#b8d3bd';ctx.font='34px "PingFang SC", sans-serif';ctx.fillText('从拓扑与分析，寻找代数几何的形状。',100,685);
  });
  // A lit door lintel and a freestanding plaque beside the entrance steps.
  const signCanvas=document.createElement('canvas');signCanvas.width=1536;signCanvas.height=384;
  const signCtx=signCanvas.getContext('2d');signCtx.fillStyle='#162724';signCtx.fillRect(0,0,1536,384);
  signCtx.fillStyle='#dfc58f';signCtx.fillRect(48,32,1440,3);signCtx.fillRect(48,349,1440,3);
  signCtx.textAlign='center';signCtx.font='118px "PingFang SC", sans-serif';signCtx.fillText('数学难民营',768,204);
  signCtx.font='30px "Times New Roman", serif';signCtx.fillText('MATHEMATICAL REFUGE',768,286);
  const signMap=new THREE.CanvasTexture(signCanvas);signMap.colorSpace=THREE.SRGBColorSpace;
  signMap.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());
  const signMaterial=new THREE.MeshStandardMaterial({map:signMap,roughness:.6,emissive:'#dfc58f',emissiveMap:signMap,emissiveIntensity:.18});
  function sign(name,position,width){
    const plaque=new THREE.Mesh(new THREE.PlaneGeometry(width,width/4),signMaterial);plaque.name=name;plaque.position.fromArray(position);scene.add(plaque);
  }
  box([0,4.23,4.07],[3.8,1.02,.16],brass);sign('Entrance lintel sign',[0,4.23,4.16],3.6);
  litStrip([0,4.78,4.14],[3.65,.035,.045]);
  box([-10.5,1.25,12.8],[4.35,1.95,.4],edge);sign('Entrance wayfinding sign',[-10.5,1.48,13.01],4);
  litStrip([-10.5,2.25,12.94],[4.12,.025,.045]);
  // Mathematical sculpture, a continuous torus knot in the entrance court.
  const sculpture=new THREE.Mesh(new THREE.TorusKnotGeometry(.85,.075,256,16,2,3),brass);
  sculpture.position.set(-.2,1.8,8);sculpture.castShadow=true;scene.add(sculpture);
  box([-.2,.53,8],[2,.5,2],edge);
  // Suspension light rings and solid metal attachment wires.
  for(const p of [[0,4.6,-1],[-5,9.15,-2],[-5,13,-3]]){
    const ring=new THREE.Mesh(new THREE.TorusGeometry(1.8,.022,8,100),light);ring.rotation.x=Math.PI/2;ring.position.fromArray(p);scene.add(ring);
    for(const a of [0,2.09,4.18])beam([p[0]+Math.cos(a)*1.7,p[1],p[2]+Math.sin(a)*1.7],[p[0]+Math.cos(a)*1.7,p[1]+.35,p[2]+Math.sin(a)*1.7],.008,steel);
  }
  // The east-facing cliff drops below sea level; land, trees and rocks never
  // continue across the water. Keep a level foundation beneath both wings.
  const seaLevel=-9;
  const coastline=z=>49+Math.sin(z*.022)*5+Math.sin(z*.081)*2;
  function elevation(x,z){
    const raw=-2.7+Math.sin(x*.048+z*.02)*3+Math.cos(z*.055)*2+Math.sin(x*.17)*Math.cos(z*.13)*.8+Math.max(0,-z-30)*.065;
    const blend=THREE.MathUtils.smoothstep(Math.max(Math.abs(x-10)/34,Math.abs(z)/20),1,1.5);
    const land=THREE.MathUtils.lerp(-2.1,raw,blend);
    const cliff=THREE.MathUtils.smoothstep(x,coastline(z)-4,coastline(z)+11);
    return THREE.MathUtils.lerp(land,-22,cliff);
  }
  const terrainGeometry=new THREE.PlaneGeometry(650,650,180,180);terrainGeometry.rotateX(-Math.PI/2);
  const positions=terrainGeometry.attributes.position,colors=new Float32Array(positions.count*3),col=new THREE.Color();
  for(let i=0;i<positions.count;i++){
    const x=positions.getX(i),z=positions.getZ(i),e=elevation(x,z);positions.setY(i,e);
    col.setHSL(.25+Math.sin(x*.03)*.02,.18,.17+Math.sin(z*.02)*.025+random()*.025);colors.set([col.r,col.g,col.b],i*3);
  }
  terrainGeometry.setAttribute('color',new THREE.BufferAttribute(colors,3));terrainGeometry.computeVertexNormals();
  const terrain=new THREE.Mesh(terrainGeometry,mat('#ffffff',1,0,{vertexColors:true}));terrain.receiveShadow=true;scene.add(terrain);
  for(let i=0;i<190;i++){
    const a=random()*Math.PI*2,r=25+random()*120,x=Math.cos(a)*r,z=Math.sin(a)*r;
    if(x>coastline(z)-12 || (x>-20&&x<53&&Math.abs(z)<21))continue;
    tree(x,elevation(x,z),z,1+random()*1.6);
  }
  // Granite clusters and background mountains anchor the building in the site.
  const rock=mat('#626b60',.96);
  for(let i=0;i<85;i++){
    const a=random()*Math.PI*2,r=19+random()*25,x=Math.cos(a)*r,z=Math.sin(a)*r,s=.6+random()*3;
    if(x>coastline(z)-5 || (x>14&&Math.abs(z)<20))continue;
    instance(sphere,rock,[x,elevation(x,z)-.2,z],[s,s*.7,s*.8],[random(),random()*6,random()]);
  }
  for(let i=0;i<13;i++){
    const x=-350+i*25,z=-180-random()*90;
    const mountain=new THREE.Mesh(new THREE.ConeGeometry(50+random()*30,30+random()*65,7),mat('#596e68',1));
    mountain.position.set(x,8,z);mountain.rotation.y=random()*6;scene.add(mountain);
  }
  // A separate animated ocean shader avoids recursively rendering two planar
  // reflection cameras. Fine normal waves, Fresnel and sun glitter are analytic;
  // this is not a fluid simulation or a photographic horizon backdrop.
  const oceanMaterial=new THREE.ShaderMaterial({
    uniforms:THREE.UniformsUtils.merge([THREE.UniformsLib.fog,{
      time:{value:0},normalMap:{value:waterNormal},sunDirection:{value:new THREE.Vector3(1,.5,.4).normalize()}
    }]),fog:true,
    vertexShader:`
      varying vec3 vWorld;
      #include <fog_pars_vertex>
      void main(){
        vec4 world=modelMatrix*vec4(position,1.0);vWorld=world.xyz;
        vec4 mvPosition=viewMatrix*world;gl_Position=projectionMatrix*mvPosition;
        #include <fog_vertex>
      }`,
    fragmentShader:`
      uniform float time;uniform sampler2D normalMap;uniform vec3 sunDirection;varying vec3 vWorld;
      #include <common>
      #include <fog_pars_fragment>
      void main(){
        vec2 uv=vWorld.xz;
        vec3 a=texture2D(normalMap,uv*.035+vec2(time*.011,-time*.007)).xyz*2.0-1.0;
        vec3 b=texture2D(normalMap,uv*.013+vec2(-time*.008,time*.005)).xyz*2.0-1.0;
        vec3 normal=normalize(vec3((a.x+b.x)*.20,1.0,(a.y+b.y)*.20));
        vec3 view=normalize(cameraPosition-vWorld);
        float fresnel=pow(1.0-max(dot(normal,view),0.0),4.0);
        float glitter=pow(max(dot(normal,normalize(sunDirection+view)),0.0),180.0);
        float swell=.5+.5*sin(uv.x*.11+uv.y*.067+time*.65);
        vec3 waterColor=mix(vec3(.016,.14,.17),vec3(.035,.25,.27),swell*.3);
        vec3 color=mix(waterColor,vec3(.48,.67,.70),fresnel*.86)+vec3(1.0,.79,.48)*glitter*2.2;
        gl_FragColor=vec4(color,1.0);
        #include <tonemapping_fragment>
        #include <colorspace_fragment>
        #include <fog_fragment>
      }`
  });
  const ocean=new THREE.Mesh(new THREE.PlaneGeometry(8000,8000),oceanMaterial);
  ocean.name='Panoramic ocean';ocean.rotation.x=-Math.PI/2;ocean.position.set(0,seaLevel,0);scene.add(ocean);
  report('正在布置光照与镜头…');
  for(const {geo,material,matrices} of batches.values()){
    const mesh=new THREE.InstancedMesh(geo,material,matrices.length);
    matrices.forEach((matrix,i)=>mesh.setMatrixAt(i,matrix));
    mesh.castShadow=material!==glass&&material!==light;mesh.receiveShadow=material!==glass;
    mesh.computeBoundingSphere();scene.add(mesh);
  }
  const sky=new Sky();sky.scale.setScalar(12000);scene.add(sky);
  sky.material.uniforms.turbidity.value=4;sky.material.uniforms.rayleigh.value=1.5;
  sky.material.uniforms.mieCoefficient.value=.005;sky.material.uniforms.mieDirectionalG.value=.8;
  const sun=new THREE.DirectionalLight('#ffdfaf',3.3);sun.castShadow=true;sun.position.set(-35,35,30);
  sun.shadow.mapSize.set(2048,2048);Object.assign(sun.shadow.camera,{left:-55,right:55,top:45,bottom:-45,near:1,far:200});
  sun.target.position.set(12,3,0);scene.add(sun.target);
  sun.shadow.normalBias=.04;sun.shadow.bias=-.00015;scene.add(sun);
  const ambient=new THREE.HemisphereLight('#b5d7e0','#514a35',1.6);scene.add(ambient);
  const interiorLights=[];
  for(const p of [[0,4,-3],[-6,8.7,-3],[-5,12.8,-3],[28,4,-4],[28,4,4],[27,8.5,-5]]){
    const lamp=new THREE.PointLight('#ffd09b',90,17,2);lamp.position.fromArray(p);scene.add(lamp);interiorLights.push(lamp);
  }
  scene.fog=new THREE.FogExp2('#9fbfc7',.00065);
  const pmrem=new THREE.PMREMGenerator(renderer);let environment;
  const envScene=new THREE.Scene();envScene.add(sky.clone());
  function lighting(value,regenerate=false){
    const t=value/100,sunDirection=new THREE.Vector3(.8,.15+t*.7,.55).normalize();
    sky.material.uniforms.sunPosition.value.copy(sunDirection);
    water.material.uniforms.sunDirection.value.copy(sunDirection);
    ocean.material.uniforms.sunDirection.value.copy(sunDirection);
    sun.position.copy(sunDirection).multiplyScalar(65);sun.intensity=1.4+t*2.5;
    ambient.intensity=.65+t*.95;sun.color.setHSL(.09,.25+(1-t)*.3,.85);
    interiorLights.forEach(l=>l.intensity=50+(1-t)*120);
    if(regenerate){environment?.dispose();environment=pmrem.fromScene(envScene,.03,.1,20000);scene.environment=environment.texture;}
  }
  lighting(62,true);
  return {water,ocean,lighting,sculpture,materials,site:{elevation,coastline,seaLevel},triangleObjects:scene.children.length,dispose(){environment?.dispose();pmrem.dispose();}};
}
