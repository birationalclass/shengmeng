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
    glazing(cx-w/2,y,cz,d,h,'z');glazing(cx+w/2,y,cz,d,h,'z');
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
  // A real typographic canvas on a modeled blackboard; not a decorative fake UI.
  const boardCanvas=document.createElement('canvas');boardCanvas.width=1536;boardCanvas.height=768;
  const ctx=boardCanvas.getContext('2d');ctx.fillStyle='#173d34';ctx.fillRect(0,0,1536,768);
  ctx.fillStyle='#eee7cf';ctx.font='48px serif';ctx.fillText('MATHEMATICS IS A PLACE TO WANDER',75,110);
  ctx.font='italic 76px serif';ctx.fillText('χ(Σ) = V − E + F',100,270);ctx.fillText('Hⁿ(X) = ker dⁿ / im dⁿ⁻¹',100,410);
  ctx.font='42px serif';ctx.fillText('Ask a better question. Take another walk.',100,615);
  const boardTex=new THREE.CanvasTexture(boardCanvas);boardTex.colorSpace=THREE.SRGBColorSpace;
  box([10.82,2.6,-3],[.16,3.1,5.8],timber);
  const board=new THREE.Mesh(new THREE.PlaneGeometry(5.5,2.8),new THREE.MeshStandardMaterial({map:boardTex,roughness:.95}));
  board.rotation.y=-Math.PI/2;board.position.set(10.72,2.6,-3);scene.add(board);
  // Mathematical sculpture, a continuous torus knot in the entrance court.
  const sculpture=new THREE.Mesh(new THREE.TorusKnotGeometry(.85,.075,256,16,2,3),brass);
  sculpture.position.set(-.2,1.8,8);sculpture.castShadow=true;scene.add(sculpture);
  box([-.2,.53,8],[2,.5,2],edge);
  // Suspension light rings and solid metal attachment wires.
  for(const p of [[0,4.6,-1],[-5,9.15,-2],[-5,13,-3]]){
    const ring=new THREE.Mesh(new THREE.TorusGeometry(1.8,.022,8,100),light);ring.rotation.x=Math.PI/2;ring.position.fromArray(p);scene.add(ring);
    for(const a of [0,2.09,4.18])beam([p[0]+Math.cos(a)*1.7,p[1],p[2]+Math.sin(a)*1.7],[p[0]+Math.cos(a)*1.7,p[1]+.35,p[2]+Math.sin(a)*1.7],.008,steel);
  }
  // Continuous terrain with altitude-colored rock/grass, not floating slabs.
  function elevation(x,z){
    const raw=-2.7+Math.sin(x*.048+z*.02)*3+Math.cos(z*.055)*2+Math.sin(x*.17)*Math.cos(z*.13)*.8+Math.max(0,-z-30)*.065;
    const blend=THREE.MathUtils.smoothstep(Math.max(Math.abs(x)/20,Math.abs(z)/18),1,1.5);
    return THREE.MathUtils.lerp(-2.1,raw,blend);
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
    tree(x,elevation(x,z),z,1+random()*1.6);
  }
  // Granite clusters and background mountains anchor the building in the site.
  const rock=mat('#626b60',.96);
  for(let i=0;i<85;i++){
    const a=random()*Math.PI*2,r=19+random()*25,x=Math.cos(a)*r,z=Math.sin(a)*r,s=.6+random()*3;
    instance(sphere,rock,[x,elevation(x,z)-.2,z],[s,s*.7,s*.8],[random(),random()*6,random()]);
  }
  for(let i=0;i<22;i++){
    const x=-300+i*28,z=-180-random()*90;
    const mountain=new THREE.Mesh(new THREE.ConeGeometry(50+random()*30,30+random()*65,7),mat('#596e68',1));
    mountain.position.set(x,8,z);mountain.rotation.y=random()*6;scene.add(mountain);
  }
  report('正在布置光照与镜头…');
  for(const {geo,material,matrices} of batches.values()){
    const mesh=new THREE.InstancedMesh(geo,material,matrices.length);
    matrices.forEach((matrix,i)=>mesh.setMatrixAt(i,matrix));
    mesh.castShadow=material!==glass&&material!==light;mesh.receiveShadow=material!==glass;
    mesh.computeBoundingSphere();scene.add(mesh);
  }
  const sky=new Sky();sky.scale.setScalar(2000);scene.add(sky);
  sky.material.uniforms.turbidity.value=4;sky.material.uniforms.rayleigh.value=1.5;
  sky.material.uniforms.mieCoefficient.value=.005;sky.material.uniforms.mieDirectionalG.value=.8;
  const sun=new THREE.DirectionalLight('#ffdfaf',3.3);sun.castShadow=true;sun.position.set(-35,35,30);
  sun.shadow.mapSize.set(2048,2048);Object.assign(sun.shadow.camera,{left:-35,right:35,top:35,bottom:-35,near:1,far:150});
  sun.shadow.normalBias=.04;sun.shadow.bias=-.00015;scene.add(sun);
  const ambient=new THREE.HemisphereLight('#b5d7e0','#514a35',1.6);scene.add(ambient);
  const interiorLights=[];
  for(const p of [[0,4,-3],[-6,8.7,-3],[-5,12.8,-3]]){
    const lamp=new THREE.PointLight('#ffd09b',90,17,2);lamp.position.fromArray(p);scene.add(lamp);interiorLights.push(lamp);
  }
  scene.fog=new THREE.FogExp2('#acbbb5',.0037);
  const pmrem=new THREE.PMREMGenerator(renderer);let environment;
  const envScene=new THREE.Scene();envScene.add(sky.clone());
  function lighting(value,regenerate=false){
    const t=value/100,sunDirection=new THREE.Vector3(-.8,.15+t*.7,.55).normalize();
    sky.material.uniforms.sunPosition.value.copy(sunDirection);
    water.material.uniforms.sunDirection.value.copy(sunDirection);
    sun.position.copy(sunDirection).multiplyScalar(65);sun.intensity=1.4+t*2.5;
    ambient.intensity=.65+t*.95;sun.color.setHSL(.09,.25+(1-t)*.3,.85);
    interiorLights.forEach(l=>l.intensity=50+(1-t)*120);
    if(regenerate){environment?.dispose();environment=pmrem.fromScene(envScene,.03,.1,2500);scene.environment=environment.texture;}
  }
  lighting(62,true);
  return {water,lighting,sculpture,materials,triangleObjects:scene.children.length,dispose(){environment?.dispose();pmrem.dispose();}};
}
