import {deferredTexture} from './deferred-textures.js?v106';
import * as THREE from 'three';
import {seaLevel,coastline,elevation,gardenElevation,canGardenPlant,slope,canPlant,shoreline,fractal,noise,seededRandom} from './landscape-shape.js?v44-hall-clearance';
import {BUILDING_SCALE,GIANT_TREES,ORNAMENTAL_TREES,BAMBOO_GROVES,LAWNS,lawnWeight,watercourse,riverPoint,inPool,inBuilding} from './site-layout.js?v44-hall-clearance';

// Real leaf/branch silhouettes, not opaque ellipsoids or billboard tree cards.
// Each species/detail prototype is built once and instanced in spatial cells.
const Y=new THREE.Vector3(0,1,0);
function builder(){
  const vertices=[],uvs=[],colors=[];
  return {
    triangle(a,b,c,color,uv=[[0,0],[1,0],[.5,1]]){for(const [i,p] of [a,b,c].entries()){vertices.push(...p.toArray());uvs.push(...uv[i]);colors.push(...color.toArray());}},
    geometry(){const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(vertices,3));g.setAttribute('uv',new THREE.Float32BufferAttribute(uvs,2));g.setAttribute('color',new THREE.Float32BufferAttribute(colors,3));g.computeVertexNormals();g.computeBoundingSphere();return g;}
  };
}
function tube(out,points,radius,endRadius,sides=7){
  const rings=[],shade=new THREE.Color('#b2a08b');
  for(let j=0;j<points.length;j++){
    const tangent=points[Math.min(j+1,points.length-1)].clone().sub(points[Math.max(j-1,0)]).normalize();
    const side=new THREE.Vector3().crossVectors(tangent,Math.abs(tangent.y)>.97?new THREE.Vector3(1,0,0):Y).normalize();
    const cross=new THREE.Vector3().crossVectors(tangent,side),ring=[];
    for(let k=0;k<sides;k++){
      const a=k/sides*Math.PI*2,r=THREE.MathUtils.lerp(radius,endRadius,j/(points.length-1))*(1+.11*Math.cos(a*3+j*.4));
      ring.push(points[j].clone().addScaledVector(side,Math.cos(a)*r).addScaledVector(cross,Math.sin(a)*r));
    }
    rings.push(ring);
  }
  for(let j=0;j<rings.length-1;j++)for(let k=0;k<sides;k++){
    const n=(k+1)%sides,u=k/sides,v=j*.5;
    out.triangle(rings[j][k],rings[j][n],rings[j+1][k],shade,[[u,v],[u+1/sides,v],[u,v+.5]]);
    out.triangle(rings[j][n],rings[j+1][n],rings[j+1][k],shade,[[u+1/sides,v],[u+1/sides,v+.5],[u,v+.5]]);
  }
}
function leaf(out,base,direction,length,width,color,flat=false){
  const axis=direction.clone().normalize(),side=new THREE.Vector3().crossVectors(axis,Math.abs(axis.y)>.96?new THREE.Vector3(1,0,0):Y).normalize();
  const mid=base.clone().addScaledVector(axis,length*.46),ridge=mid.clone().add(new THREE.Vector3(0,width*.3,0));
  const left=mid.clone().addScaledVector(side,width),right=mid.clone().addScaledVector(side,-width),tip=base.clone().addScaledVector(axis,length);
  if(flat){out.triangle(base,left,tip,color);out.triangle(tip,right,base,color);return;}
  out.triangle(base,left,ridge,color);out.triangle(left,tip,ridge,color);out.triangle(tip,right,ridge,color);out.triangle(right,base,ridge,color);
}
function olive(seed,low=false){
  const rnd=seededRandom(seed),wood=builder(),leaves=builder(),h=4.2+rnd()*.7;
  const trunk=[new THREE.Vector3(0,0,0),new THREE.Vector3(.18,h*.23,.06),new THREE.Vector3(-.17,h*.46,.14),new THREE.Vector3(.22,h*.7,-.08)];
  tube(wood,trunk,.19,.066,low?6:10);
  // Buttress roots and a forked, slightly twisted trunk.
  if(!low)for(let i=0;i<5;i++){const a=i*1.256;tube(wood,[new THREE.Vector3(Math.cos(a)*.5,.02,Math.sin(a)*.5),new THREE.Vector3(0,.58,0)],.045,.11,6);}
  for(let b=0;b<7;b++){
    const a=b*2.399+rnd()*.4,start=trunk[2].clone(),reach=1.2+rnd()*.85;
    const end=new THREE.Vector3(Math.cos(a)*reach,h*(.72+rnd()*.27),Math.sin(a)*reach);
    const mid=start.clone().lerp(end,.52).add(new THREE.Vector3(0,-.18,0));
    tube(wood,[start,mid,end],.068,.014,low?5:7);
    for(let k=0;k<(low?3:5);k++){
      const aa=a+(rnd()-.5)*2.9,base=mid.clone().lerp(end,.4+rnd()*.5);
      const tip=base.clone().add(new THREE.Vector3(Math.cos(aa)*(.45+rnd()*.6),.25+rnd()*.35,Math.sin(aa)*(.45+rnd()*.6)));
      if(!low)tube(wood,[base,tip],.016,.003,5);
      for(let j=0;j<(low?12:24);j++){
        const t=rnd(),p=base.clone().lerp(tip,t).add(new THREE.Vector3((rnd()-.5)*.56,(rnd()-.5)*.37,(rnd()-.5)*.56));
        const dir=new THREE.Vector3(Math.cos(aa+j*2.4),.2+(rnd()-.5)*1.2,Math.sin(aa+j*2.4));
        const color=new THREE.Color().setHSL(.22+rnd()*.07,.17+rnd()*.18,.26+rnd()*.2);
        leaf(leaves,p,dir,(low?.33:.23)*(1+rnd()*.6),low?.067:.037,color,low);
      }
    }
  }
  return {wood:wood.geometry(),leaf:leaves.geometry()};
}
function specimen(species){
  const wood=builder(),leaves=builder(),rnd=seededRandom(species==='terminalia'?407:811),tiered=species==='terminalia';
  tube(wood,[new THREE.Vector3(),new THREE.Vector3(.12,1.6,0),new THREE.Vector3(-.06,tiered?5:2.4,.12)],.14,.04,9);
  for(let tier=0;tier<(tiered?4:2);tier++)for(let k=0;k<6;k++){
    const a=k*Math.PI/3+tier*.63,y=tiered?2+tier*.85:1.6+tier*.7,r=tiered?2.1-tier*.29:1.5;
    const start=new THREE.Vector3(0,y,0),end=new THREE.Vector3(Math.cos(a)*r,y+(tiered?.1:.6),Math.sin(a)*r);
    tube(wood,[start,start.clone().lerp(end,.5).add(new THREE.Vector3(0,.18,0)),end],.05,.008,6);
    for(let j=0;j<50;j++){
      const t=.35+rnd()*.65,p=start.clone().lerp(end,t).add(new THREE.Vector3((rnd()-.5)*.7,(rnd()-.5)*.18,(rnd()-.5)*.7));
      leaf(leaves,p,new THREE.Vector3(Math.cos(a+j*2.4),.2,Math.sin(a+j*2.4)),tiered?.18:.32,tiered?.055:.075,new THREE.Color(tiered?(j%5?'#78915a':'#b7b988'):'#456343'));
    }
    if(!tiered)for(let f=0;f<4;f++){
      const p=end.clone().add(new THREE.Vector3((rnd()-.5)*.5,.12,(rnd()-.5)*.5));
      for(let petal=0;petal<5;petal++)leaf(leaves,p,new THREE.Vector3(Math.cos(petal*1.256),.18,Math.sin(petal*1.256)),.10,.04,new THREE.Color('#fff3ca'));
    }
  }
  return {wood:wood.geometry(),leaf:leaves.geometry()};
}
function palm(){
  const wood=builder(),leaves=builder(),rnd=seededRandom(227),points=[];
  for(let i=0;i<=10;i++)points.push(new THREE.Vector3(Math.sin(i*.13)*.65,i*.69,Math.sin(i*.2)*.27));
  tube(wood,points,.22,.1,10);
  const crown=points.at(-1);
  for(let f=0;f<11;f++){
    const a=f*2.399,frond=[];
    for(let j=0;j<=8;j++){const t=j/8;frond.push(crown.clone().add(new THREE.Vector3(Math.cos(a)*t*3,Math.sin(t*Math.PI)*.8-t*.55,Math.sin(a)*t*3)));}
    tube(wood,frond,.026,.003,5);
    for(let j=1;j<18;j++){
      const t=j/18,base=crown.clone().add(new THREE.Vector3(Math.cos(a)*t*3,Math.sin(t*Math.PI)*.8-t*.55,Math.sin(a)*t*3));
      for(const sign of [-1,1])leaf(leaves,base,new THREE.Vector3(Math.cos(a)*.4+Math.sin(a)*sign,-.3-t*.7,Math.sin(a)*.4-Math.cos(a)*sign),Math.sin(t*Math.PI)*.92+.1,.048,new THREE.Color().setHSL(.23+rnd()*.05,.35,.26+rnd()*.09));
    }
  }
  return {wood:wood.geometry(),leaf:leaves.geometry()};
}
function fern(){
  const leaves=builder(),rnd=seededRandom(977);
  for(let f=0;f<7;f++){
    const a=f*2.399;
    for(let i=1;i<=11;i++){
      const t=i/12,r=t*.65,base=new THREE.Vector3(Math.cos(a)*r,.08+Math.sin(t*Math.PI*.82)*.47,Math.sin(a)*r);
      for(const sign of [-1,1])leaf(leaves,base,new THREE.Vector3(Math.cos(a)*.55+Math.sin(a)*sign,.12,Math.sin(a)*.55-Math.cos(a)*sign),(.05+.16*Math.sin(t*Math.PI))*(1.1-t*.4),.034,new THREE.Color().setHSL(.24+rnd()*.05,.39,.2+rnd()*.1));
    }
  }
  return leaves.geometry();
}
function grass(){
  const out=builder(),rnd=seededRandom(809),color=new THREE.Color('#737d47');
  for(let i=0;i<17;i++){
    const a=rnd()*Math.PI*2,r=rnd()*.18,base=new THREE.Vector3(Math.cos(a)*r,0,Math.sin(a)*r);
    leaf(out,base,new THREE.Vector3(Math.cos(a)*.35,1,Math.sin(a)*.35),.23+rnd()*.5,.018,color);
  }
  return out.geometry();
}
function bamboo(){
  const wood=builder(),leaves=builder(),color=new THREE.Color('#7e9c55');
  for(let i=0;i<10;i++){
    const y=i*.6,x=Math.sin(i*.1)*.2,z=i*i*.0015;
    tube(wood,[new THREE.Vector3(x,y,z),new THREE.Vector3(Math.sin((i+1)*.1)*.2,y+.6,(i+1)**2*.0015)],.047-i*.002,.045-i*.002,7);
    tube(wood,[new THREE.Vector3(x,y+.02,z),new THREE.Vector3(x,y+.052,z)],.055-i*.002,.055-i*.002,7);
    if(i<4)continue;
    const a=i*2.399,base=new THREE.Vector3(x,y,z),tip=base.clone().add(new THREE.Vector3(Math.cos(a)*.75,.3,Math.sin(a)*.75));
    tube(wood,[base,tip],.009,.002,5);
    for(let j=0;j<9;j++){const t=j/9,p=base.clone().lerp(tip,t);leaf(leaves,p,new THREE.Vector3(Math.cos(a+j*2.4),.3,Math.sin(a+j*2.4)),.28,.035,color);}
  }
  return {wood:wood.geometry(),leaf:leaves.geometry()};
}
function flowers(){
  const out=builder();
  for(let k=0;k<4;k++){
    const a=k*2.399,base=new THREE.Vector3(Math.cos(a)*.1,.32+k*.04,Math.sin(a)*.1);
    for(let i=0;i<5;i++)leaf(out,base,new THREE.Vector3(Math.cos(i*1.256),.22,Math.sin(i*1.256)),.065,.035,new THREE.Color('#ffffff'));
  }
  return out.geometry();
}
function boulder(seed){
  const g=new THREE.IcosahedronGeometry(1,3),p=g.attributes.position;
  for(let i=0;i<p.count;i++){
    const x=p.getX(i),y=p.getY(i),z=p.getZ(i),r=.78+noise(x*3+seed,z*3-y)*.35;
    p.setXYZ(i,x*r,Math.max(-.65,y*r)+Math.sin(x*9+z*4)*.055,z*r);
  }
  g.computeVertexNormals();
  // Smooth shared positions without destroying spherical UV seams. The
  // deformed silhouette and photographed normal map supply the stone detail.
  const normals=g.attributes.normal,sums=new Map(),keys=[];
  for(let i=0;i<p.count;i++){
    const key=[p.getX(i),p.getY(i),p.getZ(i)].map(v=>v.toFixed(5)).join(',');keys.push(key);
    if(!sums.has(key))sums.set(key,new THREE.Vector3());sums.get(key).add(new THREE.Vector3().fromBufferAttribute(normals,i));
  }
  for(const sum of sums.values())sum.normalize();
  for(let i=0;i<p.count;i++){const n=sums.get(keys[i]);normals.setXYZ(i,n.x,n.y,n.z);}
  return g;
}

export async function createLandscape(renderer,scene,report){
  report('正在加载树皮、林地与风化岩面…');
  const textures=[],loader=new THREE.TextureLoader(),anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());
  async function load(name,srgb=false){const t=deferredTexture('./assets/'+name+'.jpg');t.wrapS=t.wrapT=THREE.RepeatWrapping;t.anisotropy=anisotropy;if(srgb)t.colorSpace=THREE.SRGBColorSpace;textures.push(t);return t;}
  const [bark,barkN,ground,groundN,rock,rockN]=await Promise.all([load('bark-color',true),load('bark-normal'),load('forest-color',true),load('forest-normal'),load('cliff-color',true),load('cliff-normal')]);
  const wood=new THREE.MeshStandardMaterial({map:bark,normalMap:barkN,normalScale:new THREE.Vector2(.65,.65),roughness:.97,vertexColors:true});
  const foliage=new THREE.MeshStandardMaterial({color:'#d1d7bc',vertexColors:true,side:THREE.DoubleSide,roughness:.86});
  const rockMaterial=new THREE.MeshStandardMaterial({color:'#969c8b',map:rock,normalMap:rockN,normalScale:new THREE.Vector2(.7,.7),roughness:.95});
  const bambooMaterial=new THREE.MeshStandardMaterial({color:'#627e36',roughness:.65,normalMap:barkN,normalScale:new THREE.Vector2(.06,.06)});
  const flowerMaterials=['#eee3b5','#b7a1ce','#c48c77'].map(color=>new THREE.MeshStandardMaterial({color,roughness:.9,side:THREE.DoubleSide}));
  const clock={value:0};
  foliage.onBeforeCompile=shader=>{
    shader.uniforms.landscapeTime=clock;
    shader.vertexShader=shader.vertexShader.replace('#include <common>','#include <common>\nuniform float landscapeTime;');
    shader.vertexShader=shader.vertexShader.replace('#include <begin_vertex>',`#include <begin_vertex>
      vec3 site=position;
      #ifdef USE_INSTANCING
        site=(instanceMatrix*vec4(position,1.0)).xyz;
      #endif
      float sway=sin(landscapeTime*.8+site.x*.27+site.z*.21);
      transformed.x+=sway*.026*min(position.y,4.0);
      transformed.z+=sin(landscapeTime*1.1+site.x*.31)*.013*min(position.y,4.0);`);
  };
  foliage.customProgramCacheKey=()=> 'refuge-leaf-breeze-v1';
  const prototypes=Array.from({length:3},(_,i)=>({near:olive(980+i*78),far:olive(980+i*78,true)}));
  const specimenPrototypes={terminalia:specimen('terminalia'),plumeria:specimen('plumeria')};
  const palmPrototype=palm(),fernGeometry=fern(),grassGeometry=grass(),rocks=[boulder(11),boulder(17),boulder(25)];
  const bambooPrototype=bamboo(),flowerGeometry=flowers();
  const ownedGeometry=new Set([fernGeometry,grassGeometry,...rocks,...Object.values(palmPrototype),...prototypes.flatMap(p=>[...Object.values(p.near),...Object.values(p.far)])]);
  for(const prototype of Object.values(specimenPrototypes))for(const g of Object.values(prototype))ownedGeometry.add(g);
  for(const g of [...Object.values(bambooPrototype),flowerGeometry])ownedGeometry.add(g);
  const batches=new Map(),dummy=new THREE.Object3D(),rnd=seededRandom(57019),plantings=[];
  function add(geometry,material,x,y,z,scale,angle,name,shadow=true){
    const cellSize=Math.hypot(x,z)>100?192:64;
    const cell=`${cellSize}:${Math.floor(x/cellSize)},${Math.floor(z/cellSize)}`,key=geometry.uuid+material.uuid+cell+name;
    if(!batches.has(key))batches.set(key,{geometry,material,matrices:[],name,shadow});
    dummy.position.set(x,y,z).multiplyScalar(BUILDING_SCALE);dummy.scale.set(...(Array.isArray(scale)?scale:[scale,scale,scale]));dummy.rotation.set(0,angle,0);dummy.updateMatrix();batches.get(key).matrices.push(dummy.matrix.clone());
  }
  function tree(x,y,z,scale=1,species='olive'){
    const distant=Math.hypot(x,z)>75,prototype=species==='palm'?palmPrototype:prototypes[Math.floor(rnd()*3)][distant?'far':'near'],a=rnd()*Math.PI*2;
    add(prototype.wood,wood,x,y,z,scale,a,'Branched bark trunks',!distant);
    add(prototype.leaf,foliage,x,y,z,scale,a,species==='giant'?'Giant tree crowns':species==='palm'?'Palm fronds':'Olive leaf canopies',!distant);
  }
  function shrub(x,y,z,scale=1){add(fernGeometry,foliage,x,y,z,scale,rnd()*6.28,'Fern understory',false);}
  function garden(){
    for(const [x,z,s] of GIANT_TREES)tree(x,.66,z,s,'giant');
    for(const [x,z,species] of ORNAMENTAL_TREES){const p=specimenPrototypes[species];add(p.wood,wood,x,.65,z,1,0,'Specimen tree trunks',true);add(p.leaf,foliage,x,.65,z,1,0,species==='terminalia'?'Tiered Terminalia inspired crowns':'White frangipani inspired crowns',true);}
    for(const [cx,cz,rx,rz] of BAMBOO_GROVES)for(let i=0;i<48;i++){
      const a=rnd()*6.28,r=Math.sqrt(rnd()),x=cx+Math.cos(a)*rx*r,z=cz+Math.sin(a)*rz*r;
      if(!canGardenPlant(x,z))continue;
      const y=gardenElevation(x,z),s=1.2+rnd()*.5,angle=rnd()*6.28;
      add(bambooPrototype.wood,bambooMaterial,x,y,z,s,angle,'Jointed bamboo stems',true);
      add(bambooPrototype.leaf,foliage,x,y,z,s,angle,'Bamboo leaf sprays',false);
      if(i%3===0)shrub(x+.4,y,z,.8);
    }
    // Actual turf surfaces, not just sparse isolated grass meshes on brown soil.
    const lawnMaterial=new THREE.MeshStandardMaterial({color:'#547740',roughness:1,normalMap:groundN,normalScale:new THREE.Vector2(.07,.07),vertexColors:true});
    extraMaterials.push(lawnMaterial);
    for(const l of LAWNS){
      const g=new THREE.PlaneGeometry(l.rx*2,l.rz*2,76,20);g.rotateX(-Math.PI/2);g.translate(l.x,0,l.z);
      const p=g.attributes.position,c=[],indices=[],color=new THREE.Color();
      for(let i=0;i<p.count;i++){const x=p.getX(i),z=p.getZ(i);p.setY(i,gardenElevation(x,z)+.026);const n=noise(x*7,z*7);color.setRGB(.68+n*.2,.8+n*.15,.58+n*.18);c.push(...color.toArray());}
      for(let i=0;i<g.index.count;i+=3){const ids=[g.index.getX(i),g.index.getX(i+1),g.index.getX(i+2)];if(ids.every(j=>lawnWeight(p.getX(j),p.getZ(j))>0))indices.push(...ids);}
      g.setIndex(indices);g.setAttribute('color',new THREE.Float32BufferAttribute(c,3));g.computeVertexNormals();ownedGeometry.add(g);
      const mesh=new THREE.Mesh(g,lawnMaterial);mesh.name='Soft lawn garden';mesh.scale.setScalar(BUILDING_SCALE);mesh.receiveShadow=true;scene.add(mesh);
      for(let i=0;i<170;i++){
        const a=rnd()*6.28,x=l.x+Math.cos(a)*l.rx*(.9+rnd()*.16),z=l.z+Math.sin(a)*l.rz*(.9+rnd()*.16);
        if(watercourse(x,z).distance<2.5||inPool(x,z,1)||inBuilding(x,z,1)||!canGardenPlant(x,z))continue;
        add(flowerGeometry,flowerMaterials[i%3],x,gardenElevation(x,z),z,.8+rnd()*.6,rnd()*6.28,'Garden flower borders',false);
        if(i%4===0)add(grassGeometry,foliage,x,gardenElevation(x,z),z,.8,rnd()*6.28,'Flower border foliage',false);
      }
    }
  }
  const extraMaterials=[];
  function populate(){
    report('正在布置海上树池、竹庭与草坪…');
    // Hero trees / palms frame the pool, leaving the steps and sea view clear.
    for(const [x,z] of [[-26,28],[-23,-29]])tree(x,gardenElevation(x,z),z,1.15,'palm');
    for(const [x,z] of [[-24,29],[-27,-28],[-26,1],[-34,5]])for(let i=0;i<4;i++)shrub(x+(rnd()-.5)*.75,gardenElevation(x,z),z+(rnd()-.5)*1.5,.65+rnd()*.25);
    for(const [x,z,s] of [[-23,29,1.4],[-27,5,1.2],[-25,-29,1.4],[-39,29,1.6]])add(rocks[0],rockMaterial,x,gardenElevation(x,z),z,[s,s*.65,s*.8],rnd()*6.28,'Garden stone outcrops');
    garden();
  }
  function finish(){
    for(const {geometry,material,matrices,name,shadow} of batches.values()){
      const mesh=new THREE.InstancedMesh(geometry,material,matrices.length);mesh.name=name;matrices.forEach((m,i)=>mesh.setMatrixAt(i,m));mesh.castShadow=shadow;mesh.receiveShadow=true;mesh.computeBoundingSphere();mesh.boundingSphere.radius+=.35;scene.add(mesh);
    }
  }
  // A small 2D depth lookup follows all three coasts rather than an east-only
  // waterline. The ocean outside this patch remains clean uninterrupted water.
  const shoreData=new Uint8Array(128*128*4);
  for(let j=0;j<128;j++)for(let i=0;i<128;i++){
    const x=-150+i/127*250,z=-110+j/127*220,depth=Math.max(0,Math.min(20,seaLevel-elevation(x,z)));
    shoreData.set([Math.round(depth/20*255),0,0,255],(j*128+i)*4);
  }
  const shoreMap=new THREE.DataTexture(shoreData,128,128);shoreMap.minFilter=shoreMap.magFilter=THREE.LinearFilter;shoreMap.needsUpdate=true;textures.push(shoreMap);
  return {tree,shrub,populate,finish,shoreMap,site:{seaLevel,coastline,elevation,slope},plantings,
    update(dt){const step=Math.max(0,Math.min(dt,.05));clock.value+=step;},
    dispose(){ownedGeometry.forEach(g=>g.dispose());textures.forEach(t=>t.dispose());[wood,foliage,rockMaterial,bambooMaterial,...flowerMaterials,...extraMaterials].forEach(m=>m?.dispose());}
  };
}
