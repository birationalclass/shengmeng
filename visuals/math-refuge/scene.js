import * as THREE from 'three';
import {RoundedBoxGeometry} from './vendor/geometries/RoundedBoxGeometry.js';
import {Water} from './vendor/objects/Water.js';
import {Sky} from './vendor/objects/Sky.js';
import {createDetailMaps} from './surface-materials.js?v=5-mobile';
import {createLandscape} from './landscape.js?v=13-room-lighting';
import {BUILDING_SCALE} from './site-layout.js?v=13-room-lighting';
import {createCampus} from './campus.js?v=13-room-lighting';
import {daylightAt,wrapHour} from './retreat-time.js?v=13-room-lighting';
import {platformUnion} from './platform-union.js?v=13-room-lighting';

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
  const details=createDetailMaps(renderer.capabilities.getMaxAnisotropy());
  const steel=mat('#1d2526',.88,.3,{roughnessMap:details.brushedRoughness,envMapIntensity:.3}),stone=mat('#92978b',.94,0,{map:stoneMap,normalMap:stoneNormal,roughnessMap:stoneRough,normalScale:new THREE.Vector2(.12,.12),envMapIntensity:.25}),edge=mat('#111f20',.83,.1,{normalMap:details.plasterNormal,normalScale:new THREE.Vector2(.13,.13)});
  const brass=mat('#bda27c',.82,.35,{roughnessMap:details.brushedRoughness,envMapIntensity:.3}),timber=mat('#968064',.94,0,{map:woodMap,normalMap:woodNormal,normalScale:new THREE.Vector2(.16,.16),roughnessMap:woodRough});
  const cloth={normalMap:details.clothNormal,roughnessMap:details.clothRoughness,normalScale:new THREE.Vector2(.28,.28)};
  const pale=mat('#c3b59d',.98,0,cloth),darkFabric=mat('#465955',1,0,cloth),soil=mat('#302d21',1),leaf=mat('#46734e',.9);
  const ceramic=mat('#d6cab6',.65),glass=new THREE.MeshPhysicalMaterial({color:'#c3e7dc',roughness:.3,metalness:0,ior:1.3,specularIntensity:.2,envMapIntensity:.22,transparent:true,opacity:.11,depthWrite:false,side:THREE.FrontSide});
  const light=mat('#dac6a5',.95,0,{emissive:'#d7b685',emissiveIntensity:.5});
  const blackboard=mat('#153f38',.95),ink=mat('#dddcc5',1);
  const materials={steel,stone,edge,brass,timber,pale,darkFabric,soil,leaf,glass,light,blackboard,ink};
  const landscape=await createLandscape(renderer,scene,report);
  const boxes=new THREE.BoxGeometry(1,1,1),roundedCache=new Map();
  const cylinder=new THREE.CylinderGeometry(1,1,1,12);
  const rubber=mat('#0e1b18',.97);
  const batches=new Map(),dummy=new THREE.Object3D(),layoutFloors=[];
  function instance(geo,material,p,s,r=[0,0,0]){
    const key=geo.uuid+material.uuid;if(!batches.has(key))batches.set(key,{geo,material,matrices:[]});
    dummy.position.fromArray(p);dummy.scale.fromArray(s);dummy.rotation.set(...r);dummy.updateMatrix();
    batches.get(key).matrices.push(dummy.matrix.clone());
  }
  const box=(p,s,m=stone,r)=>instance(boxes,m,p,s,r);
  const soft=(p,s,m=pale,r)=>{
    const key=s.join(',');
    if(!roundedCache.has(key))roundedCache.set(key,new RoundedBoxGeometry(...s,2,Math.min(...s)*.22));
    instance(roundedCache.get(key),m,p,[1,1,1],r);
  };
  function beam(a,b,radius,material=steel){
    const av=new THREE.Vector3(...a),bv=new THREE.Vector3(...b),mid=av.clone().add(bv).multiplyScalar(.5),direction=bv.clone().sub(av);
    const q=new THREE.Quaternion().setFromUnitVectors(new THREE.Vector3(0,1,0),direction.clone().normalize());
    const rot=new THREE.Euler().setFromQuaternion(q);instance(cylinder,material,mid.toArray(),[radius,direction.length(),radius],[rot.x,rot.y,rot.z]);
  }
  function litStrip(p,size){box(p,size,light);}
  function floor(y,w,d,cx=0,cz=0){
    layoutFloors.push({y,w,d,cx,cz});
  }
  const platformGeometries=[];
  function buildPlatforms(){
    for(const y of new Set(layoutFloors.map(f=>f.y))){
      const rects=layoutFloors.filter(f=>f.y===y).map(f=>[f.cx-f.w/2,f.cx+f.w/2,f.cz-f.d/2,f.cz+f.d/2]);
      const union=platformUnion(rects),top=[],sides=[];
      const quad=(out,a,b,c,d)=>out.push(...a,...b,...c,...a,...c,...d);
      for(const [a,b,c,d] of union.cells){
        quad(top,[a,y+.275,c],[a,y+.275,d],[b,y+.275,d],[b,y+.275,c]);
        quad(sides,[a,y-.2,c],[b,y-.2,c],[b,y-.2,d],[a,y-.2,d]);
      }
      for(const [a,c,b,d] of union.edges)quad(sides,[a,y-.2,c],[a,y+.275,c],[b,y+.275,d],[b,y-.2,d]);
      for(const [positions,material,name] of [[top,stone,'Unified platform top'],[sides,edge,'Unified platform fascia']]){
        const geometry=new THREE.BufferGeometry(),uv=[];
        for(let i=0;i<positions.length;i+=3)uv.push(positions[i]*.08,positions[i+2]*.08);
        geometry.setAttribute('position',new THREE.Float32BufferAttribute(positions,3));geometry.setAttribute('uv',new THREE.Float32BufferAttribute(uv,2));geometry.computeVertexNormals();
        const mesh=new THREE.Mesh(geometry,material);mesh.name=name+' '+y;mesh.receiveShadow=true;mesh.castShadow=true;scene.add(mesh);architectureObjects.add(mesh);platformGeometries.push(geometry);
        mesh.userData.cells=union.cells;
      }
    }
  }
  function glazing(x,y,z,width,height,axis='x'){
    const s=axis==='x'?[width,height,.035]:[.035,height,width];
    box([x,y+height/2,z],s,glass);
    const n=Math.ceil(width/2);
    for(let i=0;i<=n;i++){
      const k=(i/n-.5)*width;box([x+(axis==='x'?k:0),y+height/2,z+(axis==='x'?0:k)],[.075,height,.075],steel);
    }
    for(const h of [0,height])box([x,y+h,z],axis==='x'?[width,.09,.11]:[.11,.09,width],steel);
    // Recessed dark seals sit inside the metal head/sill instead of more glass
    // layers (which would add costly transparent overdraw on mobile).
    for(const h of [.07,height-.07])box([x,y+h,z],axis==='x'?[width,.022,.052]:[.052,.022,width],rubber);
  }
  function railing(x,y,z,w,axis='x'){
    glazing(x,y,z,w,1.05,axis);
    box([x,y+1.08,z],axis==='x'?[w,.045,.05]:[.05,.045,w],brass);
  }
  function planter(x,y,z,w=2){
    box([x,y+.24,z],[w,.48,.9],edge);box([x,y+.48,z],[w-.13,.03,.75],soil);
    for(let i=0;i<Math.ceil(w*2);i++){
      const px=x+(random()-.5)*(w-.1),pz=z+(random()-.5)*.7;
      landscape.shrub(px,y+.5,pz,(.52+random()*.2)*BUILDING_SCALE);
    }
  }
  function tree(x,y,z,scale=1){
    landscape.tree(x,y,z,scale*BUILDING_SCALE);
  }
  function sofa(x,y,z,angle=0){
    const group=new THREE.Group();group.position.set(x,y,z);group.rotation.y=angle;
    // Transform upholstered modules into the common instancing batches.
    const part=(p,s,m)=>{const v=new THREE.Vector3(...p).divideScalar(BUILDING_SCALE).applyAxisAngle(new THREE.Vector3(0,1,0),angle).add(group.position);soft(v.toArray(),s.map(d=>d/BUILDING_SCALE),m,[0,angle,0]);};
    part([0,.21,0],[3.1,.34,1.1],edge);part([0,.56,-.48],[3.05,.85,.27],darkFabric);
    for(const a of [-1,0,1]){
      part([a,.46,.04],[.96,.22,.91],pale);part([a,.73,-.25],[.86,.56,.23],pale);
      part([a,.565,.405],[.83,.012,.012],darkFabric);
    }
    part([-1.52,.52,0],[.22,.55,1.1],darkFabric);part([1.52,.52,0],[.22,.55,1.1],darkFabric);
    for(const px of [-1.2,1.2])for(const pz of [-.35,.35])part([px,.06,pz],[.09,.15,.09],brass);
  }
  function table(x,y,z,w=2,d=1){
    const p=(a,b,c)=>[x+a/BUILDING_SCALE,y+b/BUILDING_SCALE,z+c/BUILDING_SCALE],s=a=>a.map(v=>v/BUILDING_SCALE);
    soft(p(0,.57,0),s([w,.12,d]),timber);
    for(const dx of [-w*.36,w*.36])for(const dz of [-d*.33,d*.33])box(p(dx,.28,dz),s([.075,.55,.075]),brass);
    // Closed notebooks and ceramic bowl.
    box(p(-.2,.66,0),s([.4,.055,.3]),blackboard);
    instance(cylinder,ceramic,p(.4,.72,0),s([.13,.19,.13]));
  }
  report('正在搭建环绕泳池、小拱桥与海上报告厅…');
  const campus=createCampus(scene,{box,soft,beam,floor,glazing,railing,sofa,table,planter,instance,cylinder,materials,Water,waterNormal});
  const {water}=campus;
  // Independent chalkboards, with brief mathematical statements rather than
  // unverified solved/unsolved status announcements.
  function chalkboard(name,x,rotation,draw){
    const canvas=document.createElement('canvas');canvas.width=1536;canvas.height=768;
    const ctx=canvas.getContext('2d');ctx.fillStyle='#173d34';ctx.fillRect(0,0,1536,768);draw(ctx);
    const map=new THREE.CanvasTexture(canvas);map.colorSpace=THREE.SRGBColorSpace;
    map.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());
    const backing=x-Math.sin(rotation)*.1;
    box([backing,1.35,-3],[.12,1.8,4.2],timber);
    const board=new THREE.Mesh(new THREE.PlaneGeometry(4,1.65),new THREE.MeshPhysicalMaterial({map,color:'#c9c5bb',roughness:1,metalness:0,specularIntensity:0,envMapIntensity:0,emissive:0x000000,emissiveIntensity:0}));
    board.name=name;board.rotation.y=rotation;board.position.set(x,1.35,-3);scene.add(board);
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
  chalkboard('NS conjecture blackboard',-.15,-Math.PI/2,ctx=>{
    fracturedNS(ctx);
    ctx.fillStyle='#eee7cf';ctx.font='72px "PingFang SC", sans-serif';ctx.fillText('NS 方程 · 存在性与光滑性',85,115);
    ctx.font='64px "Times New Roman", serif';ctx.fillText('∂ₜu + (u · ∇)u = νΔu − ∇p',100,255);ctx.fillText('∇ · u = 0,     u(x, 0) = u₀(x)',100,355);
    ctx.font='42px "PingFang SC", sans-serif';ctx.fillStyle='#b8d3bd';ctx.fillText('三维、无外力、周期边界，ν > 0。',100,470);
    ctx.fillStyle='#eee7cf';ctx.fillText('任意光滑且散度为零的初始速度，',100,565);ctx.fillText('能否产生对所有时间都保持光滑的解？',100,635);
  });
  chalkboard('Hodge conjecture blackboard',-11.85,Math.PI/2,ctx=>{
    ctx.fillStyle='#eee7cf';ctx.font='82px "PingFang SC", sans-serif';ctx.fillText('Hodge 猜想 ？',85,130);
    ctx.font='48px "PingFang SC", sans-serif';ctx.fillText('在光滑复射影簇 X 上，',100,290);
    ctx.fillText('每个有理的 (p, p) 型上同调类，',100,385);
    ctx.fillText('是否都是余维 p 的代数子簇之类',100,480);ctx.fillText('的有理线性组合？',100,565);
    ctx.fillStyle='#b8d3bd';ctx.font='34px "PingFang SC", sans-serif';ctx.fillText('从拓扑与分析，寻找代数几何的形状。',100,685);
  });
  // One campus logo at the arrival gate; every room has its own function sign.
  function sign(name,position,width,title,subtitle,rotation=0){
    const canvas=document.createElement('canvas');canvas.width=1536;canvas.height=384;
    const ctx=canvas.getContext('2d');ctx.fillStyle='#162724';ctx.fillRect(0,0,1536,384);
    ctx.fillStyle='#dfc58f';ctx.fillRect(48,32,1440,3);ctx.fillRect(48,349,1440,3);
    ctx.textAlign='center';ctx.font='118px "PingFang SC", sans-serif';ctx.fillText(title,768,204);
    ctx.font='30px "Times New Roman", serif';ctx.fillText(subtitle,768,286);
    const map=new THREE.CanvasTexture(canvas);map.colorSpace=THREE.SRGBColorSpace;map.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());
    const material=new THREE.MeshStandardMaterial({map,roughness:.6,emissive:'#dfc58f',emissiveMap:map,emissiveIntensity:.18});
    const plaque=new THREE.Mesh(new THREE.PlaneGeometry(width,width/4),material);plaque.name=name;plaque.userData.label=title;plaque.position.fromArray(position);plaque.rotation.y=rotation;scene.add(plaque);
  }
  box([-6,2.13,5.1],[3.8,.65,.16],brass);sign('Entrance lintel sign',[-6,2.13,5.2],3.6,'学术客厅','ACADEMIC LOUNGE');
  sign('Conference entrance sign',[39,2.65,10.1],2.4,'报告厅','SEMINAR HALL');
  sign('Discussion entrance sign',[11.5,2.1,5.12],2.8,'讨论室','DISCUSSION ROOM');
  sign('Library entrance sign',[-37,2,-10.88],2.8,'图书馆','LIBRARY');
  sign('Residence one sign',[-51.88,1.9,-28],2.1,'研究员居所 Ⅰ','RESIDENCE I',Math.PI/2);
  sign('Residence two sign',[-42.88,1.9,-38],2.1,'研究员居所 Ⅱ','RESIDENCE II',Math.PI/2);
  sign('Tea kitchen sign',[-30.88,1.9,19],2.1,'茶室 · 服务','TEA & SERVICE',Math.PI/2);
  sign('Garden tea sign',[-35,2.2,-26.45],2,'竹庭茶亭','GARDEN TEA PAVILION');
  litStrip([-6,2.5,5.17],[3.65,.025,.025]);
  floor(0,5,3,-68,10);
  box([-68,1.25,10],[4.35,1.95,.4],edge);sign('Entrance wayfinding sign',[-68,1.48,10.21],4,'数学难民营','MATHEMATICAL REFUGE');
  litStrip([-68,2.25,10.14],[4.12,.025,.045]);
  // Mathematical sculpture, a continuous torus knot in the entrance court.
  const sculpture=new THREE.Mesh(new THREE.TorusKnotGeometry(.85,.075,256,16,2,3),brass);
  sculpture.position.set(-5,1.6,10);sculpture.castShadow=true;scene.add(sculpture);
  box([-5,.53,10],[2,.5,2],edge);
  // Room-specific pendant/cove fixtures are constructed with their rooms.
  // Only offshore architecture and contained garden planting remain.
  const {seaLevel,elevation,coastline}=landscape.site;
  const architectureObjects=new Set(scene.children);
  landscape.populate();landscape.finish();
  // A separate animated ocean shader avoids recursively rendering two planar
  // reflection cameras. Fine normal waves, Fresnel and sun glitter are analytic;
  // this is not a fluid simulation or a photographic horizon backdrop.
  const oceanMaterial=new THREE.ShaderMaterial({
    uniforms:THREE.UniformsUtils.merge([THREE.UniformsLib.fog,{
      time:{value:0},siteScale:{value:BUILDING_SCALE},normalMap:{value:waterNormal},shoreMap:{value:landscape.shoreMap},sunDirection:{value:new THREE.Vector3(1,.5,.4).normalize()}
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
      uniform float time;uniform float siteScale;uniform sampler2D normalMap;uniform sampler2D shoreMap;uniform vec3 sunDirection;varying vec3 vWorld;
      #include <common>
      #include <fog_pars_fragment>
      void main(){
        vec2 uv=vWorld.xz/siteScale;
        vec3 a=texture2D(normalMap,uv*.035+vec2(time*.011,-time*.007)).xyz*2.0-1.0;
        vec3 b=texture2D(normalMap,uv*.013+vec2(-time*.008,time*.005)).xyz*2.0-1.0;
        vec3 normal=normalize(vec3((a.x+b.x)*.20,1.0,(a.y+b.y)*.20));
        vec3 view=normalize(cameraPosition-vWorld);
        float fresnel=pow(1.0-max(dot(normal,view),0.0),4.0);
        float glitter=pow(max(dot(normal,normalize(sunDirection+view)),0.0),180.0);
        float swell=.5+.5*sin(uv.x*.11+uv.y*.067+time*.65);
        vec3 waterColor=mix(vec3(.016,.14,.17),vec3(.035,.25,.27),swell*.3);
        vec2 shoreUV=vec2((uv.x+150.0)/250.0,(uv.y+110.0)/220.0);
        float inPatch=step(0.0,shoreUV.x)*step(shoreUV.x,1.0)*step(0.0,shoreUV.y)*step(shoreUV.y,1.0);
        float shoreDistance=texture2D(shoreMap,clamp(shoreUV,0.0,1.0)).r*20.0;
        float nearShore=(1.0-smoothstep(.2,8.0,shoreDistance))*inPatch;
        waterColor=mix(waterColor,vec3(.06,.30,.27),nearShore*.7);
        float foam=pow(.5+.5*sin(shoreDistance*2.2-time*.9+a.x*.7),8.0)*exp(-shoreDistance*.58)*nearShore;
        vec3 color=mix(waterColor,vec3(.28,.41,.43),fresnel*.45)+vec3(1.0,.79,.48)*glitter*.22;
        color=mix(color,vec3(.67,.77,.71),foam*.45);
        gl_FragColor=vec4(color,1.0);
        #include <tonemapping_fragment>
        #include <colorspace_fragment>
        #include <fog_fragment>
      }`
  });
  const ocean=new THREE.Mesh(new THREE.PlaneGeometry(8000,8000),oceanMaterial);
  ocean.name='Panoramic ocean';ocean.rotation.x=-Math.PI/2;ocean.position.set(0,seaLevel*BUILDING_SCALE,0);scene.add(ocean);
  report('正在布置光照与镜头…');
  buildPlatforms();
  for(const {geo,material,matrices} of batches.values()){
    const mesh=new THREE.InstancedMesh(geo,material,matrices.length);
    matrices.forEach((matrix,i)=>mesh.setMatrixAt(i,matrix));
    mesh.castShadow=material!==glass&&material!==light;mesh.receiveShadow=material!==glass;
    mesh.computeBoundingSphere();scene.add(mesh);architectureObjects.add(mesh);
  }
  for(const object of architectureObjects){object.scale.multiplyScalar(BUILDING_SCALE);object.position.multiplyScalar(BUILDING_SCALE);object.userData.architectureScale=BUILDING_SCALE;}
  const sky=new Sky();sky.scale.setScalar(12000);scene.add(sky);
  sky.material.uniforms.turbidity.value=4;sky.material.uniforms.rayleigh.value=1.5;
  sky.material.uniforms.mieCoefficient.value=.005;sky.material.uniforms.mieDirectionalG.value=.8;
  const sun=new THREE.DirectionalLight('#ffdfaf',3.3);sun.castShadow=true;sun.position.set(-35,35,30);
  sun.shadow.mapSize.set(2048,2048);Object.assign(sun.shadow.camera,{left:-55*BUILDING_SCALE,right:55*BUILDING_SCALE,top:45*BUILDING_SCALE,bottom:-45*BUILDING_SCALE,near:1,far:200*BUILDING_SCALE});
  sun.target.position.set(12,3,0).multiplyScalar(BUILDING_SCALE);scene.add(sun.target);
  sun.shadow.normalBias=.065;sun.shadow.bias=-.0002;scene.add(sun);
  const ambient=new THREE.HemisphereLight('#b5d7e0','#514a35',1.6);scene.add(ambient);
  const interiorLights=[];
  for(const zone of campus.lightingZones){
    const lamp=new THREE.SpotLight(zone.color,70,14*BUILDING_SCALE,Math.PI*.38,.85,2);
    lamp.name=zone.name+' warm downlight';lamp.userData.gain=zone.gain;
    lamp.position.fromArray(zone.position);
    if(zone.fixture)zone.fixture.add(lamp);else{lamp.position.multiplyScalar(BUILDING_SCALE);scene.add(lamp);}
    lamp.target.position.fromArray(zone.target).multiplyScalar(BUILDING_SCALE);
    scene.add(lamp.target);interiorLights.push(lamp);
  }
  scene.fog=new THREE.FogExp2('#9fbfc7',.0015);
  const pmrem=new THREE.PMREMGenerator(renderer);let environment;
  const envScene=new THREE.Scene();envScene.add(sky.clone());
  function lighting(value,regenerate=false){
    const t=value/100,sunDirection=new THREE.Vector3(1,.04+t*.6,0).normalize();
    sky.material.uniforms.sunPosition.value.copy(sunDirection);
    water.material.uniforms.sunDirection.value.copy(sunDirection);
    ocean.material.uniforms.sunDirection.value.copy(sunDirection);
    sun.position.copy(sunDirection).multiplyScalar(65*BUILDING_SCALE);sun.intensity=1.4+t*2.5;
    ambient.intensity=.65+t*.95;sun.color.setHSL(.09,.25+(1-t)*.3,.85);
    interiorLights.forEach(l=>l.intensity=(24+(1-t)*44)*BUILDING_SCALE**2*l.userData.gain);
    if(regenerate){environment?.dispose();environment=pmrem.fromScene(envScene,.03,.1,20000);scene.environment=environment.texture;}
  }
  function setTime(hour,regenerate=false){
    const h=wrapHour(hour),day=daylightAt(h),a=(h-6)*Math.PI/12;
    const direction=new THREE.Vector3(Math.cos(a),Math.sin(a),0).normalize();
    sky.material.uniforms.sunPosition.value.copy(direction);water.material.uniforms.sunDirection.value.copy(direction);ocean.material.uniforms.sunDirection.value.copy(direction);
    sun.position.copy(direction).multiplyScalar(65*BUILDING_SCALE);sun.intensity=day*2.1;sun.color.setHSL(.095,.28+(1-day)*.25,.85);
    ambient.intensity=.18+day*1.1;interiorLights.forEach(l=>l.intensity=(24+(1-day)*44)*BUILDING_SCALE**2*l.userData.gain);
    light.emissiveIntensity=.35+(1-day)*.3;scene.environmentIntensity=.12+day*.5;
    scene.fog.color.set('#9fbfc7').lerp(new THREE.Color('#101b2b'),1-day);
    if(regenerate){environment?.dispose();environment=pmrem.fromScene(envScene,.03,.1,20000);scene.environment=environment.texture;}
  }
  setTime(8,true);
  return {water,ocean,sun,lighting,setTime,sculpture,materials,landscape,campus,layoutFloors,site:{elevation:(x,z)=>elevation(x/BUILDING_SCALE,z/BUILDING_SCALE)*BUILDING_SCALE,coastline:z=>coastline(z/BUILDING_SCALE)*BUILDING_SCALE,seaLevel:seaLevel*BUILDING_SCALE},triangleObjects:scene.children.length,dispose(){platformGeometries.forEach(g=>g.dispose());campus.dispose();landscape.dispose();environment?.dispose();pmrem.dispose();Object.values(details).forEach(map=>map.dispose());}};
}
