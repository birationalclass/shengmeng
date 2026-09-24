import {createBeachMaterial} from './beach-material.js?v91-shore';
import {apparentSunDirection} from './solar-optics.js?v88-solar-water';
import {sunWaterVisibility} from './graphics-settings.js?v84-display';
import {withDeadline} from './mobile-runtime.js?v79-mobile';
import {advanceWeatherWinds,windVelocity} from './cloud-wind.js?v88-solar-water';
import {createResidence} from './residence.js?v82-steady';
import {createRain} from './weather-rain.js?v72-night-rain';
import {roundedDetailLevel} from './render-budget.js?v84-display';
import * as THREE from 'three';
import {createBoats} from './boats.js?v88-solar-water';
import {createOpenBook} from './book-sculpture.js?v=36-board-detail';
import {createRoomFill} from './room-fill.js?v81-imac';
import {createPathLighting} from './path-lighting.js?v44-hall-clearance';
import {RoundedBoxGeometry} from './vendor/geometries/RoundedBoxGeometry.js';
import {createWeatherSky} from './weather-sky.js?v88-solar-water';
import {solarState,shanghaiHour,smooth} from './solar-state.js?v88-solar-water';
import {seaDepthGLSL,seaDepthAt} from './sea-depth.js?v91-shore';
import {createDetailMaps} from './surface-materials.js?v=5-mobile';
import {createLandscape} from './landscape.js?v44-hall-clearance';
import {BUILDING_SCALE,DECK_Y,HALL} from './site-layout.js?v44-hall-clearance';
import {createDistantIslands} from './distant-islands.js?v44-hall-clearance';
import {createCampus} from './campus.js?v76-villa';
import {daylightAt,wrapHour,localHour} from './retreat-time.js?v=20-slower-tour';
import {platformUnion} from './platform-union.js?v=20-slower-tour';

export async function createRetreat(renderer,scene,report,device={}){
  let seed=82573;
  const random=()=>{seed=(seed*1664525+1013904223)>>>0;return seed/4294967296;};
  const loader=new THREE.TextureLoader();
  async function texture(name,repeat=1,srgb=false){
    const map=await withDeadline(loader.loadAsync('./assets/'+name),20000,'材质 '+name);map.wrapS=map.wrapT=THREE.RepeatWrapping;
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
  const smartGlass=glass.clone();smartGlass.name='Seamless low-iron smart glass';smartGlass.roughness=.08;smartGlass.opacity=.075;smartGlass.color.set('#d5eef0');
  const light=mat('#dac6a5',.95,0,{emissive:'#d7b685',emissiveIntensity:.5});
  const blackboard=mat('#153f38',.95),ink=mat('#dddcc5',1);
  const materials={steel,stone,edge,brass,timber,pale,darkFabric,soil,leaf,glass,smartGlass,light,blackboard,ink};
  const landscape=await createLandscape(renderer,scene,report);
  const boxes=new THREE.BoxGeometry(1,1,1),roundedCache=new Map();
  const cylinder=new THREE.CylinderGeometry(1,1,1,12);
  const rubber=mat('#0e1b18',.97);
  const batches=new Map(),dummy=new THREE.Object3D(),layoutFloors=[];
  function instance(geo,material,p,s,r=[0,0,0]){
    // A campus-wide material batch defeats frustum culling: seeing one chair
    // used to submit the chairs and fittings in every building and storey.
    if(!geo.boundingSphere)geo.computeBoundingSphere();

    const region=p[0]<-76?'seminar:'+Math.floor(p[1]/3):p[0]>30?'hall:'+Math.floor(p[1]/3):'campus';
    const key=geo.uuid+material.uuid+region;
    if(!batches.has(key))batches.set(key,{geo,material,matrices:[],region});
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
  const terraceBase=mat('#686458',1,0,{map:stoneMap,normalMap:stoneNormal,normalScale:new THREE.Vector2(.04,.04),envMapIntensity:.1});
  const platformGeometries=[];
  function buildPlatforms(){
    for(const y of new Set(layoutFloors.map(f=>f.y))){
      const rects=layoutFloors.filter(f=>f.y===y).map(f=>[f.cx-f.w/2,f.cx+f.w/2,f.cz-f.d/2,f.cz+f.d/2]);
      const union=platformUnion(rects),top=[],sides=[],bottom=y===0?seaLevel-.2:y-.2;
      const quad=(out,a,b,c,d)=>out.push(...a,...b,...c,...a,...c,...d);
      for(const [a,b,c,d] of union.cells){
        quad(top,[a,y+.275,c],[a,y+.275,d],[b,y+.275,d],[b,y+.275,c]);
        quad(sides,[a,bottom,c],[b,bottom,c],[b,bottom,d],[a,bottom,d]);
      }
      for(const [a,c,b,d] of union.edges){
        quad(sides,[a,bottom,c],[a,y+.275,c],[b,y+.275,d],[b,bottom,d]);
        const length=Math.hypot(b-a,d-c);if(length>.03)box([(a+b)/2,y+.245,(c+d)/2],[Math.abs(b-a)||.018,.022,Math.abs(d-c)||.018],pathLighting.material);
      }
      for(const [positions,material,name] of [[top,terraceBase,'Unified platform top'],[sides,edge,'Unified platform fascia']]){
        const geometry=new THREE.BufferGeometry(),uv=[];
        for(let i=0;i<positions.length;i+=3)uv.push(positions[i]*.08,positions[i+2]*.08);
        geometry.setAttribute('position',new THREE.Float32BufferAttribute(positions,3));geometry.setAttribute('uv',new THREE.Float32BufferAttribute(uv,2));geometry.computeVertexNormals();
        const mesh=new THREE.Mesh(geometry,material);mesh.name=name+' '+y;mesh.receiveShadow=true;mesh.castShadow=true;scene.add(mesh);architectureObjects.add(mesh);platformGeometries.push(geometry);
        mesh.userData.cells=union.cells;
      }
    }
  }
  function glazing(x,y,z,width,height,axis='x',style={}){
    const frame=style.frame||.075,n=style.panels||Math.ceil(width/(style.spacing||2));
    if(style.panels){
      const gap=style.seal||.006,pane=width/n;
      for(let i=0;i<n;i++){
        const k=(i+.5)*pane-width/2;
        const clearWidth=n===1?width:pane-gap;
        box([x+(axis==='x'?k:0),y+height/2,z+(axis==='x'?0:k)],axis==='x'?[clearWidth,height,.024]:[.024,height,clearWidth],smartGlass);
      }
      for(let i=1;i<n;i++){
        const k=(i/n-.5)*width;box([x+(axis==='x'?k:0),y+height/2,z+(axis==='x'?0:k)],[gap,height,gap],rubber);
      }
      for(const k of [-width/2,width/2])box([x+(axis==='x'?k:0),y+height/2,z+(axis==='x'?0:k)],[frame,height,frame],steel);
    }else{
      box([x,y+height/2,z],axis==='x'?[width,height,.035]:[.035,height,width],glass);
      for(let i=0;i<=n;i++){
        const k=(i/n-.5)*width;box([x+(axis==='x'?k:0),y+height/2,z+(axis==='x'?0:k)],[frame,height,frame],steel);
      }
    }
    for(const h of [0,height])box([x,y+h,z],axis==='x'?[width,frame,frame]:[frame,frame,width],steel);
    // Recessed dark seals sit inside the metal head/sill instead of more glass
    // layers (which would add costly transparent overdraw on mobile).
    for(const h of [.07,height-.07])box([x,y+h,z],axis==='x'?[width,style.seal||.022,frame*.7]:[frame*.7,style.seal||.022,width],rubber);
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
  report('正在搭建海上长露台与报告厅…');
  const campus=createCampus(scene,{box,soft,beam,floor,glazing,railing,sofa,table,planter,instance,cylinder,materials});
  const pathLighting=createPathLighting(scene,{box,beam,materials});
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
  sign('Conference entrance sign',[(HALL.west+HALL.east)/2,2.65,HALL.south+.1],2.4,'报告厅','SEMINAR HALL');
  sign('Coffee cabin sign',[39,2,-18.9],2.3,'咖啡小屋','COFFEE CABIN');
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
  // A coherent family of large mathematical door sculptures, offset from
  // entrances and sea-access stairs. Shared knot geometry bounds draw cost.
  const sculptureGeometry=new Map(),sculptures=[];
  const sculptureEntries=[
    ['Academic lounge',-5,10,2,3],
    ['Discussion room',14.5,9.5,2,5],
    ['Residence I',-50.5,-25.5,2,3],['Residence II',-41.5,-35.5,2,5],
    ['Tea service',-28.8,21.5,3,4],['Tea pavilion',-38.7,-25.8,3,5],
    ['Arrival gate',-69.8,13.2,2,3]
  ];
  for(const [x,z,w,d] of [[-39,-9.1,6,4.6],[-50.5,-25.5,3.6,3.6],[-41.5,-35.5,3.6,3.6],[-28.8,21,4.8,4.2],[-38.7,-25.8,3.6,3.6],[-69,12,5,6]])floor(0,w,d,x,z);
  for(const [name,x,z,p,q] of sculptureEntries){
    const key=p+':'+q;
    if(!sculptureGeometry.has(key)){const g=new THREE.TorusKnotGeometry(.78,.075,160,12,p,q);g.computeBoundingBox();sculptureGeometry.set(key,g);}
    const geometry=sculptureGeometry.get(key),mesh=new THREE.Mesh(geometry,brass);
    mesh.name=name+' mathematical sculpture';mesh.position.set(x,DECK_Y+.5-geometry.boundingBox.min.y,z);
    mesh.castShadow=true;mesh.receiveShadow=true;mesh.userData={facility:name,footprint:[x-1.3,x+1.3,z-1.3,z+1.3]};
    scene.add(mesh);sculptures.push(mesh);box([x,DECK_Y+.25,z],[2.6,.5,2.6],edge);
  }
  const libraryBook=createOpenBook(),book=libraryBook.book;
  book.position.set(-40.5,DECK_Y+.51,-8.2);book.rotation.y=.12;
  book.userData={...book.userData,facility:'Library',footprint:[-41.8,-39.2,-9.5,-6.9]};scene.add(book);sculptures.push(book);
  box([-40.5,DECK_Y+.25,-8.2],[2.6,.5,2.6],edge);
  const sculpture=sculptures[0];
  // Room-specific pendant/cove fixtures are constructed with their rooms.
  // Only offshore architecture and contained garden planting remain.
  const {seaLevel,elevation,coastline}=landscape.site;
  const architectureObjects=new Set(scene.children);
  landscape.populate();landscape.finish();
  const islands=createDistantIslands(scene);
  // Only the ocean remains: there is no pool mesh or planar reflection pass.
  // Fine normal waves, Fresnel and sun glitter are analytic;
  // this is not a fluid simulation or a photographic horizon backdrop.
  const oceanMaterial=new THREE.ShaderMaterial({
    uniforms:THREE.UniformsUtils.merge([THREE.UniformsLib.fog,{
      oceanCameraWorld:{value:new THREE.Matrix4()},oceanInverseProjection:{value:new THREE.Matrix4()},oceanProjection:{value:new THREE.Matrix4()},oceanLevel:{value:seaLevel*BUILDING_SCALE},windWaves:{value:1},waveStrength:{value:.5},reflectionDetail:{value:1},sunReflection:{value:1},windFlow:{value:new THREE.Vector2(1,0)},waveOffset:{value:new THREE.Vector2()},windSpeed:{value:2},skyDay:{value:1},skyCoverage:{value:0},skyStorm:{value:0},waterDetail:{value:1},skyMap:{value:null},skyCloudMap:{value:null},skyCloudPrevious:{value:null},skyCloudBlend:{value:1},skyCloudEnabled:{value:0},skyPhysical:{value:0},solarRadius:{value:.00465},sunTint:{value:new THREE.Color('#fff4df')},sunStrength:{value:1},rainAmount:{value:0},overcast:{value:0},time:{value:0},nightVisibility:{value:1},siteScale:{value:BUILDING_SCALE},normalMap:{value:waterNormal},shoreMap:{value:landscape.shoreMap},sunDirection:{value:new THREE.Vector3(1,.5,.4).normalize()}
    }]),fog:true,
    vertexShader:`
      uniform mat4 oceanCameraWorld,oceanInverseProjection;
      varying vec3 oceanRay;
      void main(){
        vec4 viewRay=oceanInverseProjection*vec4(position.xy,1.,1.);
        oceanRay=mat3(oceanCameraWorld)*viewRay.xyz;
        gl_Position=vec4(position.xy,0.,1.);
      }`,
    fragmentShader:`
      uniform float windWaves,waveStrength,reflectionDetail,sunReflection;uniform vec2 windFlow,waveOffset;uniform float windSpeed,skyDay,skyCoverage,skyStorm;uniform sampler2D skyMap,skyCloudMap,skyCloudPrevious;uniform float skyPhysical,skyCloudBlend,skyCloudEnabled,solarRadius,waterDetail;uniform vec3 sunTint;uniform float sunStrength,overcast,rainAmount;uniform float time;uniform float nightVisibility;uniform float siteScale;uniform sampler2D normalMap;uniform sampler2D shoreMap;uniform vec3 sunDirection;uniform float oceanLevel;uniform mat4 oceanProjection;varying vec3 oceanRay;
      #include <common>
      #include <fog_pars_fragment>
      ${seaDepthGLSL}
      vec2 waveHash(vec2 p){return fract(sin(vec2(dot(p,vec2(127.1,311.7)),dot(p,vec2(269.5,183.3))))*43758.5453);}
      vec3 scatteredNormal(vec2 p){
        vec2 cell=floor(p*.7),f=fract(p*.7);f=f*f*(3.-2.*f);
        vec2 dx=dFdx(p),dy=dFdy(p);
        vec3 n00=textureGrad(normalMap,p+waveHash(cell)*19.,dx,dy).xyz;
        vec3 n10=textureGrad(normalMap,p+waveHash(cell+vec2(1,0))*19.,dx,dy).xyz;
        vec3 n01=textureGrad(normalMap,p+waveHash(cell+vec2(0,1))*19.,dx,dy).xyz;
        vec3 n11=textureGrad(normalMap,p+waveHash(cell+vec2(1,1))*19.,dx,dy).xyz;
        return mix(mix(n00,n10,f.x),mix(n01,n11,f.x),f.y)*2.-1.;
      }
      // Analytic shallow-water height field. Gradients bend rays; Hessians focus them.
      void rippleField(vec2 p,out vec2 gradient,out mat2 curvature){
        gradient=vec2(0.);curvature=mat2(0.);
        for(int i=0;i<5;i++){
          float k=float(i),angle=.43+k*2.399963;
          vec2 direction=vec2(cos(angle),sin(angle));
          float frequency=4.3+k*1.37,amplitude=.047/(1.+k*.24);
          float phase=dot(p,direction)*frequency-time*sqrt(9.81*frequency)+k*1.37;
          gradient+=direction*(amplitude*frequency*cos(phase));
          float bend=-amplitude*frequency*frequency*sin(phase);
          curvature+=mat2(direction.x*direction.x,direction.x*direction.y,direction.x*direction.y,direction.y*direction.y)*bend;
        }
      }
      float sandCaustic(vec2 bottom,float depth){
        vec2 p=bottom,gradient;mat2 curvature;float travel=min(depth,2.5)*.25;
        // Two bounded inverse-ray iterations estimate the water entry point for this sand point.
        for(int i=0;i<2;i++){rippleField(p,gradient,curvature);p=bottom-clamp(gradient*travel,vec2(-.35),vec2(.35));}
        rippleField(p,gradient,curvature);
        mat2 jacobian=mat2(1.)+curvature*travel;
        float area=abs(jacobian[0][0]*jacobian[1][1]-jacobian[0][1]*jacobian[1][0]);
        // Finite sun footprint prevents singular, razor-sharp or unbounded light lines.
        return 1.5*exp(-area*area/.025);
      }
      vec3 grazingSky(vec2 heading){
        vec2 hUV=vec2(.5+atan(heading.y,heading.x)/6.28318530718,0.);
        vec3 h=mix(vec3(.07,.24,.43)*nightVisibility,texture2D(skyMap,hUV).rgb+vec3(.006,.013,.027)*(1.-skyDay),skyPhysical);
        h=mix(h,vec3(.33,.39,.47)*(.025+.975*skyDay),skyCoverage*skyStorm*.68);
        vec4 c=mix(texture2D(skyCloudPrevious,hUV),texture2D(skyCloudMap,hUV),skyCloudBlend);
        return h*(1.-c.a*skyCloudEnabled)+c.rgb*skyCloudEnabled;
      }
      void main(){
        vec3 rayDirection=normalize(oceanRay);
        if(rayDirection.y>=-.0000001||cameraPosition.y<=oceanLevel)discard;
        float travel=(oceanLevel-cameraPosition.y)/rayDirection.y;
        vec3 vWorld=cameraPosition+rayDirection*travel;
        vec4 projected=oceanProjection*viewMatrix*vec4(vWorld,1.);
        gl_FragDepthEXT=min(.9999995,.5*projected.z/projected.w+.5);
        vec2 uv=vWorld.xz/siteScale;
        // Restore the earlier two counter-moving normal layers; their clocks are real-time.
        vec2 drift=waveOffset*windWaves;
        vec2 waveUV=uv*.035+vec2(time*.011,-time*.007)-drift*.007;
        vec2 bend=vec2(sin(uv.y*.023+sin(uv.x*.017)),sin(uv.x*.019+sin(uv.y*.013)))*.09;
        vec3 a=mix(texture2D(normalMap,waveUV+bend).xyz*2.-1.,scatteredNormal(waveUV+bend),.25);
        vec3 b=vec3(0.);if(waterDetail>.5)b=texture2D(normalMap,mat2(.7986,-.6018,.6018,.7986)*uv*.0173+vec2(-time*.008,time*.005)-drift*.005).xyz*2.-1.;
        float windGain=smoothstep(0.,14.,windSpeed)*windWaves;
        float effectiveWave=min(1.5,max(.5,waveStrength)+.8*windGain);
        float chop=mix(.20,.28,windGain)*effectiveWave;
        vec2 crossWind=vec2(-windFlow.y,windFlow.x);
        vec2 slopes=windFlow*(a.x+b.x)+crossWind*(a.y+b.y);
        slopes+=(windFlow*cos(dot(uv,windFlow)*.095-time*.61)
          +normalize(windFlow+crossWind*.73)*cos(dot(uv,windFlow+crossWind*.73)*.057-time*.43+1.7)*.57
          +normalize(windFlow-crossWind*.41)*cos(dot(uv,windFlow-crossWind*.41)*.137-time*.79+4.1)*.31)*.06*windGain;
        float surfaceDistance=length(vWorld.xz-cameraPosition.xz);
        float footprint=max(length(dFdx(uv)),length(dFdy(uv)));
        float detailFade=inversesqrt(1.+pow(surfaceDistance/650.,2.))*inversesqrt(1.+pow(footprint/.65,2.));
        vec2 rippleGradient;mat2 rippleCurvature;
        float beachInfluence=exp(-max(seaDepthAt(uv),0.)*.32);
        if(beachInfluence>.001){rippleField(vWorld.xz,rippleGradient,rippleCurvature);slopes=mix(slopes,-rippleGradient*.55/max(chop,.001),beachInfluence*.18);}
        vec3 normal=normalize(vec3(slopes.x*chop*detailFade,1.,slopes.y*chop*detailFade));
        // Expanding impact rings have staggered births and fade before cell edges.
        vec2 cell=floor(vWorld.xz*.65),local=fract(vWorld.xz*.65)-.5;
        float seed=fract(sin(dot(cell,vec2(127.1,311.7)))*43758.5453),age=fract(time*1.6+seed),r=length(local);
        float ring=exp(-pow((r-age*.42)/.025,2.))*(1.-age)*smoothstep(0.,.08,age)*(1.-smoothstep(.37,.48,r));
        normal=normalize(normal+vec3(local.x,0.,local.y)*ring*rainAmount*.22*detailFade);
        vec3 view=normalize(cameraPosition-vWorld);
        float nv=max(dot(normal,view),.001);
        float fresnel=.0204+.9796*pow(1.0-nv,5.0);
        vec3 halfVector=normalize(sunDirection+view);float nh=max(dot(normal,halfVector),0.0);
        // GGX slope distribution; finite solar disk broadens the glint continuously.
        float alpha=.012+.055*windGain+solarRadius*.45+rainAmount*.025,a2=alpha*alpha;
        float distribution=a2/(3.14159265*pow(nh*nh*(a2-1.)+1.,2.));
        float nl=max(dot(normal,sunDirection),0.0),k=alpha*.5;
        float visibility=nv/(nv*(1.-k)+k)*nl/(nl*(1.-k)+k);
        float sunF=.0204+.9796*pow(1.-max(dot(view,halfVector),0.),5.);
        // Bound radiance smoothly; avoid a flat clipped white column at grazing angles.
        float radiance=distribution*visibility*sunF/(4.*nv+.001);
        float glitter=1.1*(1.-exp(-radiance*.4));
        float swell=.5+.5*sin(uv.x*.11+uv.y*.067+time*.65);
        float depth=seaDepthAt(uv);if(depth<.005)discard;
        vec3 transmission=exp(-vec3(.23,.105,.065)*depth);
        vec3 waterColor=vec3(.006,.065,.12)*(1.0-transmission)+vec3(.25,.37,.28)*transmission;
        waterColor*=.94+swell*.06;
        // One depth-driven optical model across the shelf: no beach-mask colour seam.
        float sand=exp(-depth*.16);
        if(sand>.001){
          vec2 bottom=uv-normal.xz*depth*.35;
          vec3 clarity=exp(-vec3(.42,.19,.12)*depth);
          vec3 sandColor=vec3(.54,.49,.36);
          vec3 shallow=sandColor*clarity+vec3(.008,.29,.34)*(1.-clarity);
          float caustic=sandCaustic(bottom*siteScale,depth)*exp(-surfaceDistance/180.)/(1.+pow(footprint/.4,2.));
          shallow+=vec3(.20,.27,.23)*caustic*exp(-depth*.6)*sunStrength;
          waterColor=mix(waterColor,shallow,sand);
        }
        vec2 shoreUV=vec2((uv.x+150.0)/250.0,(uv.y+110.0)/220.0);
        float inPatch=step(0.0,shoreUV.x)*step(shoreUV.x,1.0)*step(0.0,shoreUV.y)*step(shoreUV.y,1.0);
        float shoreDistance=texture2D(shoreMap,clamp(shoreUV,0.0,1.0)).r*20.0;
        float nearShore=(1.0-smoothstep(.2,8.0,shoreDistance))*inPatch;
        waterColor=mix(waterColor,vec3(.06,.30,.27),nearShore*.16);
        float foam=pow(.5+.5*sin(shoreDistance*2.2-time*.9+a.x*.7),8.0)*exp(-shoreDistance*.58)*nearShore;
        float wash=pow(max(0.,sin(depth*10.-time*.55+sin(uv.x*.21+uv.y*.13))),10.);
        foam=max(foam,beachMask(uv)*wash*exp(-depth*4.)*(.25+.35*a.x)*.4);
        vec3 reflection=reflect(-view,normal);reflection.y=max(.002,reflection.y);
        vec2 reflectedUV=vec2(.5+atan(reflection.z,reflection.x)/6.28318530718,sqrt(clamp(asin(clamp(reflection.y,0.,1.))/1.57079632679,0.,1.)));
        vec3 reflected=mix(vec3(.07,.24,.43)*nightVisibility,texture2D(skyMap,reflectedUV).rgb,skyPhysical);
        reflected=mix(reflected,vec3(.33,.39,.47)*(.025+.975*skyDay),skyCoverage*skyStorm*.68);
        vec4 clouds=vec4(0.);if(reflectionDetail>.5)clouds=mix(texture2D(skyCloudPrevious,reflectedUV),texture2D(skyCloudMap,reflectedUV),skyCloudBlend);
        reflected=reflected*(1.-clouds.a*skyCloudEnabled)+clouds.rgb*skyCloudEnabled;
        reflected+=vec3(.002,.004,.009)*(1.-nightVisibility);
        vec3 color=waterColor*nightVisibility*(1.-fresnel)+reflected*fresnel+sunTint*glitter*sunStrength*sunReflection;
        color=mix(color,vec3(.67,.77,.71),foam*.45*nightVisibility);
        float distanceToEye=length(vWorld.xz-cameraPosition.xz);
        vec3 horizonColor=grazingSky(-view.xz)*mix(vec3(.76,.84,.89),vec3(.94),skyStorm);
        float aerial=1.-exp(-fogDensity*fogDensity*distanceToEye*distanceToEye);
        float edgeFade=smoothstep(20000.,100000.,distanceToEye);
        color=mix(color,horizonColor,max(aerial,edgeFade));
        gl_FragColor=vec4(color,1.0);
        #include <tonemapping_fragment>
        #include <colorspace_fragment>
      }`
  });
  const ocean=new THREE.Mesh(new THREE.PlaneGeometry(2,2),oceanMaterial);
  ocean.name='Panoramic ocean';ocean.position.y=seaLevel*BUILDING_SCALE;ocean.frustumCulled=false;ocean.raycast=()=>{};
  ocean.onBeforeRender=(_renderer,_scene,camera)=>{const u=oceanMaterial.uniforms;u.oceanCameraWorld.value.copy(camera.matrixWorld);u.oceanInverseProjection.value.copy(camera.projectionMatrixInverse);u.oceanProjection.value.copy(camera.projectionMatrix);};scene.add(ocean);
  // The east terrace ends at x=54; beach profile and optical depth share one model.
  const sandGeometry=new THREE.PlaneGeometry(90*BUILDING_SCALE,93*BUILDING_SCALE,180,186);
  sandGeometry.rotateX(-Math.PI/2);const sandPositions=sandGeometry.attributes.position;
  for(let i=0;i<sandPositions.count;i++){const x=39+sandPositions.getX(i)/BUILDING_SCALE,z=sandPositions.getZ(i)/BUILDING_SCALE;sandPositions.setXYZ(i,x*BUILDING_SCALE,seaLevel*BUILDING_SCALE-seaDepthAt(x,z),z*BUILDING_SCALE);}
  sandGeometry.computeVertexNormals();const sandSurface=createBeachMaterial(seaLevel*BUILDING_SCALE),sandMaterial=sandSurface.material;
  const beach=new THREE.Mesh(sandGeometry,sandMaterial);beach.name='Irregular auditorium sand shelf';beach.receiveShadow=true;scene.add(beach);
  report('正在布置光照与镜头…');
  buildPlatforms();
  const lodBatches=[],lowGeometry=new Map();
  for(const {geo,material,matrices,region} of batches.values()){
    const mesh=new THREE.InstancedMesh(geo,material,matrices.length);
    matrices.forEach((matrix,i)=>mesh.setMatrixAt(i,matrix));
    mesh.castShadow=material!==glass&&material!==smartGlass&&material!==light&&material!==pathLighting.material;mesh.receiveShadow=material!==glass&&material!==smartGlass;
    mesh.computeBoundingSphere();mesh.computeBoundingBox();mesh.userData.spatialRegion=region;
    scene.add(mesh);architectureObjects.add(mesh);
    if(geo.type==='RoundedBoxGeometry'&&geo.parameters.segments>1){
      if(!lowGeometry.has(geo)){const p=geo.parameters;lowGeometry.set(geo,new RoundedBoxGeometry(p.width,p.height,p.depth,1,p.radius));}
      mesh.userData.lodLevel=0;lodBatches.push({mesh,high:geo,low:lowGeometry.get(geo),radius:geo.boundingSphere.radius*BUILDING_SCALE});
    }
  }
  for(const object of architectureObjects){object.scale.multiplyScalar(BUILDING_SCALE);object.position.multiplyScalar(BUILDING_SCALE);object.userData.architectureScale=BUILDING_SCALE;}
  for(const item of lodBatches){item.mesh.updateMatrixWorld();item.bounds=item.mesh.boundingBox.clone().applyMatrix4(item.mesh.matrixWorld);}
  function updateGeometryLOD(camera,viewportHeight,full=false){
    const focal=viewportHeight*camera.zoom/(2*Math.tan(camera.fov*Math.PI/360));
    for(const item of lodBatches){
      const pixels=item.radius*focal/Math.max(.1,item.bounds.distanceToPoint(camera.position));
      const level=full?0:roundedDetailLevel(pixels,item.mesh.userData.lodLevel);
      if(level!==item.mesh.userData.lodLevel){item.mesh.geometry=level?item.low:item.high;item.mesh.userData.lodLevel=level;}
    }
  }
  const residence=createResidence(scene,materials);
  const roomFill=createRoomFill();roomFill.apply(scene);
  const fleet=createBoats(scene);
  const rain=createRain(scene);
  const sky=createWeatherSky({renderer,device});sky.material.uniforms.seaHorizon.value=1;
  // Opaque architecture writes depth first. Hidden water/sky fragments can then
  // fail early depth testing instead of shading through classroom walls/boards.
  // Transparent glass still draws afterwards; no geometry is hidden or removed.
  ocean.renderOrder=900;sky.renderOrder=1000;scene.add(sky);
  const sun=new THREE.DirectionalLight('#ffdfaf',3.3);sun.castShadow=true;sun.position.set(-35,35,30);
  sun.shadow.mapSize.set(2048,2048);Object.assign(sun.shadow.camera,{left:-55*BUILDING_SCALE,right:55*BUILDING_SCALE,top:45*BUILDING_SCALE,bottom:-45*BUILDING_SCALE,near:1,far:200*BUILDING_SCALE});
  sun.target.position.set(12,3,0).multiplyScalar(BUILDING_SCALE);scene.add(sun.target);
  sun.shadow.normalBias=.018;sun.shadow.bias=-.00008;scene.add(sun);
  const ambient=new THREE.HemisphereLight('#b5d7e0','#514a35',1.6);scene.add(ambient);
  const interiorLights=[];
  for(const zone of campus.lightingZones){
    const lamp=zone.type==='point'?new THREE.PointLight(zone.color,1,(zone.range||12)*BUILDING_SCALE,2):new THREE.SpotLight(zone.color,1,(zone.range||12)*BUILDING_SCALE,zone.angle||Math.PI*.38,.85,2);
    lamp.name=zone.name+(zone.type==='point'?' warm bounce':' warm downlight');lamp.castShadow=false;lamp.userData.gain=zone.gain;lamp.userData.power=zone.power||190;lamp.userData.task=zone.task||'ambient';
    lamp.position.fromArray(zone.position);
    if(zone.fixture)zone.fixture.add(lamp);else{lamp.position.multiplyScalar(BUILDING_SCALE);scene.add(lamp);}
    if(lamp.isSpotLight){lamp.target.position.fromArray(zone.target).multiplyScalar(BUILDING_SCALE);scene.add(lamp.target);}
    interiorLights.push(lamp);
  }
  scene.fog=new THREE.FogExp2('#8dbbdf',.00028);
  // One neutral diffuse reflection probe; never swap discrete half-hour snapshots.
  // Directional light, sky, water highlights and probe strength evolve continuously.
  const pmrem=new THREE.PMREMGenerator(renderer);let environment;
  const envScene=new THREE.Scene(),probe=createWeatherSky({panorama:false,renderer,device,probe:true});probe.material.uniforms.showSun.value=0;probe.material.uniforms.cloud.value=.18;envScene.add(probe);
  environment=pmrem.fromScene(envScene,.03,.1,20000);scene.environment=environment.texture;probe.geometry.dispose();probe.material.dispose();
  const weather={cloud:.14,rain:0,fog:0,wind:8,windDirection:225},weatherTarget={...weather};let skySeconds=0;const cloudWind={velocity:windVelocity(8,225),offset:{x:0,z:0}},waterWind={velocity:windVelocity(8,225),offset:{x:0,z:0}};
  const warmColor=new THREE.Color('#ff7334'),noonColor=new THREE.Color('#fff4e0'),fogDay=new THREE.Color('#477b9c'),fogNight=new THREE.Color('#101b2b');
  function setWeather(value){Object.assign(weatherTarget,{cloud:value?.cloud??.14,rain:value?.rain??0,fog:value?.fog??0,wind:value?.wind??weatherTarget.wind,windDirection:Number.isFinite(value?.windDirection)?value.windDirection:weatherTarget.windDirection});}
  function setTime(hour,regenerate=false,dt=0,weatherRate=1,date=new Date()){
    sandSurface.update(dt);const state=solarState(hour,date),day=state.daylight,k=dt>0?1-Math.exp(-dt/4):1;
    for(const key of Object.keys(weather))if(key!=='windDirection')weather[key]+=(weatherTarget[key]-weather[key])*k;weather.windDirection=weatherTarget.windDirection;advanceWeatherWinds(cloudWind,waterWind,weatherTarget.wind,weatherTarget.windDirection,dt,weatherRate);
    const cloud=weather.cloud,storm=smooth(.4,1,cloud),sunThrough=1-.86*storm;
    const u=sky.material.uniforms;u.sunPosition.value.fromArray(state.direction);u.sunColor.value.copy(noonColor).lerp(warmColor,state.warm);u.day.value=day;u.warm.value=state.warm;u.direct.value=state.direct;u.cloud.value=cloud;u.storm.value=storm;u.radius.value=state.radius*(sky.userData.solarSize==='physical'?1:2+(1-smooth(0,14,Math.abs(state.elevation)))*smooth(-.1,.1,state.direction[0]));u.stars.value=state.night;u.sidereal.value=hour*Math.PI/12;skySeconds+=dt*(.3+weather.wind/25);u.clock.value=skySeconds;u.cloudOffset.value.set(cloudWind.offset.x,cloudWind.offset.z);
    roomFill.setDaylight(day*(1-.3*storm));pathLighting.update(day);
    ocean.material.uniforms.rainAmount.value=Math.min(1,weather.rain/3);ocean.material.uniforms.nightVisibility.value=.06+day*.94;ocean.material.uniforms.sunDirection.value.fromArray(state.direction);ocean.material.uniforms.sunTint.value.copy(u.sunColor.value);ocean.material.uniforms.sunStrength.value=state.direct*sunThrough;ocean.material.uniforms.overcast.value=storm;
    sun.position.copy(sun.target.position).addScaledVector(u.sunPosition.value,90*BUILDING_SCALE);sun.intensity=state.direct*(.8+2.2*smooth(0,60,state.elevation))*sunThrough;sun.color.copy(u.sunColor.value);
    ambient.intensity=.18+day*(1.15-.28*storm);ambient.color.set('#91beeb').lerp(new THREE.Color('#d0d5df'),storm*.7);ambient.groundColor.set('#423d33');
    const lamps=1-smooth(.16,.7,day);interiorLights.forEach(l=>l.intensity=l.userData.power*(.22+lamps*.78)*BUILDING_SCALE**2*l.userData.gain);
    light.emissiveIntensity=.45+lamps*1.05;scene.environmentIntensity=.08+day*(.52-.16*storm);
    scene.fog.density=.000018+.00023*(1-day)+.00032*storm+.0012*weather.fog;
    scene.fog.color.copy(fogDay).lerp(fogNight,1-day).lerp(new THREE.Color('#929eac'),storm*.4*day);
    u.seaColor.value.copy(scene.fog.color);sky.userData.updateAtmosphere();
    const water=ocean.material.uniforms;water.skyMap.value=u.atmosphereMap.value;water.skyPhysical.value=u.useAtmosphere.value;water.skyCloudMap.value=u.cloudMap.value;water.skyCloudPrevious.value=u.cloudMapPrevious.value;water.skyCloudBlend.value=u.cloudBlend.value;water.skyCloudEnabled.value=u.useVolumeClouds.value;water.solarRadius.value=state.radius;
    water.skyDay.value=day;water.skyCoverage.value=cloud;water.skyStorm.value=storm;
    const vx=waterWind.velocity.x,vz=waterWind.velocity.z,windLength=Math.hypot(vx,vz);
    if(windLength>.000001)water.windFlow.value.set(vx/windLength,vz/windLength);
    water.windSpeed.value=weather.wind/3.6;water.waveOffset.value.set(waterWind.offset.x*1000/BUILDING_SCALE*.45,waterWind.offset.z*1000/BUILDING_SCALE*.45);
    const apparent=apparentSunDirection(state.direction);water.sunDirection.value.fromArray(apparent);water.sunStrength.value=sunWaterVisibility(apparent[1],state.radius)*(.22+.78*state.direct)*sunThrough;
    sky.userData.state={hour,elevation:state.elevation,cloud,day,sunIntensity:sun.intensity};
  }
  function lighting(value){setTime(6+Math.max(0,Math.min(100,value))/100*6);}
  setTime(shanghaiHour(),true);
  return {residence,rain,weather,updateGeometryLOD,ocean,islands,fleet,sculptures,sun,sky,lighting,setTime,setWeather,roomFill,pathLighting,sculpture,materials,landscape,campus,layoutFloors,site:{elevation:(x,z)=>elevation(x/BUILDING_SCALE,z/BUILDING_SCALE)*BUILDING_SCALE,coastline:z=>coastline(z/BUILDING_SCALE)*BUILDING_SCALE,seaLevel:seaLevel*BUILDING_SCALE},triangleObjects:scene.children.length,dispose(){sandGeometry.dispose();sandMaterial.dispose();residence.dispose();rain.dispose();lowGeometry.forEach(g=>g.dispose());fleet.dispose();libraryBook.dispose();islands.dispose();pathLighting.dispose();sculptureGeometry.forEach(g=>g.dispose());terraceBase.dispose();platformGeometries.forEach(g=>g.dispose());campus.dispose();landscape.dispose();sky.geometry.dispose();sky.material.dispose();environment?.dispose();pmrem.dispose();Object.values(details).forEach(map=>map.dispose());}};
}
