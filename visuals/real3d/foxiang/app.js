import * as THREE from 'three';
import { OrbitControls } from '../../3d/vendor/OrbitControls.js';
import { GLTFLoader } from '../vendor/GLTFLoader.js';
import { DRACOLoader } from '../vendor/DRACOLoader.js';
import { Sky } from '../vendor/Sky.js';
import { Water } from '../vendor/Water.js';

const $ = id => document.getElementById(id);
const stage=$('stage'), canvas=$('scene'), status=$('status');
const reduced=matchMedia('(prefers-reduced-motion: reduce)').matches;
let renderer, controls, scene, camera, model, water, sun, envTarget;
let ready=false, mode='3d', dirty=true, transition=null, frame=0, currentView='pool';
const views={
 pool:{position:[13,30,110],target:[0,14,-1]},
 terrace:{position:[27,34,28],target:[0,24,-5]},
 overview:{position:[100,92,110],target:[0,9,-4]},
 back:{position:[65,52,-94],target:[0,17,-5]}
};
const error=message=>{
 $('loading').hidden=false;$('loadingTitle').textContent='场景暂时未能打开';
 $('loadStatus').textContent=message;$('progress').hidden=true;$('retry').hidden=false;
 status.textContent=message;stage.dataset.ready='error';
};
$('retry').onclick=()=>location.reload();
function setStatus(){status.textContent=ready?'场景已就绪 · 可自由旋转与缩放':'等待场景载入';}
function invalidate(){dirty=true;}
function setView(key,immediate=false){
 if(!controls)return;
 currentView=key;$('orbit').checked=false;controls.autoRotate=false;
 const v=views[key];
 transition={start:performance.now(),from:camera.position.clone(),fromTarget:controls.target.clone(),to:new THREE.Vector3(...v.position),toTarget:new THREE.Vector3(...v.target)};
 if(immediate||reduced){camera.position.copy(transition.to);controls.target.copy(transition.toTarget);transition=null;controls.update();}
 document.querySelectorAll('[data-view]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.view===key)));
 setMode('3d');invalidate();
}
function setMode(value){
 mode=value;$('reference').hidden=value!=='render';
 document.querySelectorAll('[data-mode]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.mode===value)));
 $('modeLabel').innerHTML=value==='3d'?'<i></i> 实时三维':'静态精修 · 1920 × 1280';
 $('gestureHint').hidden=value==='render';
 if(controls)controls.enabled=value==='3d'&&ready;
 if(value==='render'){$('loading').hidden=true;status.textContent='Blender 渲染图 · 返回自由探索即可旋转';}
 else{if(!ready)$('loading').hidden=false;setStatus();}
 invalidate();
}
function resize(){if(!renderer)return;const r=stage.getBoundingClientRect();renderer.setSize(r.width,r.height,false);camera.aspect=r.width/r.height;camera.updateProjectionMatrix();invalidate();}
function quality(){
 if(!renderer)return;
 const v=$('quality').value;
 renderer.setPixelRatio(Math.min(devicePixelRatio,v==='high'?2:v==='low'?1:1.4));
 renderer.shadowMap.enabled=v!=='low';
 if(model)model.traverse(o=>{if(o.name.startsWith('Forest_scanned_tree')&&Number(o.name.match(/\d+/)?.[0])%2)o.visible=v!=='low';});
 resize();
}
function waterNormals(){
 const n=128, data=new Uint8Array(n*n*4);
 for(let j=0;j<n;j++)for(let i=0;i<n;i++){
  const x=i/n*Math.PI*2,y=j/n*Math.PI*2;
  const dx=.25*Math.cos(x*5+y*3)+.12*Math.cos(x*11-y*7),dy=.2*Math.cos(x*5+y*3)-.14*Math.cos(x*11-y*7);
  const v=new THREE.Vector3(-dx*.08,1,-dy*.08).normalize(),k=(j*n+i)*4;
  data[k]=(v.x*.5+.5)*255;data[k+1]=(v.z*.5+.5)*255;data[k+2]=(v.y*.5+.5)*255;data[k+3]=255;
 }
 const t=new THREE.DataTexture(data,n,n,THREE.RGBAFormat);t.wrapS=t.wrapT=THREE.RepeatWrapping;t.magFilter=t.minFilter=THREE.LinearFilter;t.needsUpdate=true;return t;
}
function prepareMaterials(root){
 const touched=new Set();
 root.traverse(o=>{
  if(!o.isMesh)return;
  const foliage=/tree|shrub|foliage|leaves/i.test(o.name);
  o.castShadow=!foliage;o.receiveShadow=true;
  for(const m of Array.isArray(o.material)?o.material:[o.material]){
   if(touched.has(m))continue;touched.add(m);
   if(m.map)m.map.anisotropy=Math.min(4,renderer.capabilities.getMaxAnisotropy());
   m.envMapIntensity=.035;
   if(/Architectural glass/i.test(m.name)){
    m.transmission=0;m.transparent=true;m.opacity=.22;m.depthWrite=false;m.roughness=.055;m.metalness=.08;m.envMapIntensity=1.2;
   }
   if(m.alphaMap||m.alphaTest>0){m.alphaTest=.45;m.transparent=false;m.side=THREE.DoubleSide;}
   m.needsUpdate=true;
  }
 });
}
async function init(){
 try{
  renderer=new THREE.WebGLRenderer({canvas,antialias:true,alpha:false,powerPreference:'high-performance'});
  renderer.outputColorSpace=THREE.SRGBColorSpace;renderer.toneMapping=THREE.ACESFilmicToneMapping;renderer.toneMappingExposure=.75;
  renderer.shadowMap.enabled=true;renderer.shadowMap.type=THREE.PCFSoftShadowMap;
  scene=new THREE.Scene();scene.background=new THREE.Color('#bdced5');scene.fog=new THREE.Fog('#c3d2d7',240,700);
  camera=new THREE.PerspectiveCamera(38,1,.2,1200);
  controls=new OrbitControls(camera,canvas);controls.enableDamping=true;controls.dampingFactor=.075;controls.minDistance=8;controls.maxDistance=350;controls.minPolarAngle=.10;controls.maxPolarAngle=Math.PI*.49;controls.autoRotateSpeed=.32;controls.maxTargetRadius=90;controls.cursor.set(0,14,-1);
  controls.addEventListener('change',()=>{invalidate();canvas.dataset.camera=camera.position.toArray().map(n=>n.toFixed(2)).join(',');});
  controls.addEventListener('start',()=>{transition=null;controls.autoRotate=false;$('orbit').checked=false;document.querySelectorAll('[data-view]').forEach(b=>b.setAttribute('aria-pressed','false'));});
  scene.add(new THREE.HemisphereLight(0xdae9f6,0x796951,.40));
  sun=new THREE.DirectionalLight(0xffe0b2,2.5);sun.position.set(-70,100,80);sun.target.position.set(0,8,0);sun.castShadow=true;
  Object.assign(sun.shadow.camera,{left:-95,right:95,top:95,bottom:-95,near:1,far:300});sun.shadow.mapSize.set(2048,2048);sun.shadow.normalBias=.035;sun.shadow.bias=-.00008;scene.add(sun,sun.target);
  const sky=new Sky();sky.scale.setScalar(600);const u=sky.material.uniforms;u.turbidity.value=3;u.rayleigh.value=1.3;u.mieCoefficient.value=.004;u.mieDirectionalG.value=.8;u.sunPosition.value.copy(sun.position).normalize();
  const envScene=new THREE.Scene();envScene.add(sky);const pmrem=new THREE.PMREMGenerator(renderer);envTarget=pmrem.fromScene(envScene,.03,.1,1000);scene.environment=envTarget.texture;pmrem.dispose();sky.geometry.dispose();sky.material.dispose();
  // The exported scene is in metres. Blender Z-up becomes glTF Y-up.
  water=new Water(new THREE.PlaneGeometry(360,128),{textureWidth:512,textureHeight:512,waterNormals:waterNormals(),sunDirection:sun.position.clone().normalize(),sunColor:0xffe4bc,waterColor:0x204446,distortionScale:.22,alpha:.88,fog:true});
  water.material.fragmentShader=water.material.fragmentShader.replace('float rf0 = 0.3;', 'float rf0 = 0.02;');water.material.needsUpdate=true;
  water.rotation.x=-Math.PI/2;water.position.set(0,-.29,94);water.material.uniforms.size.value=2.5;scene.add(water);
  const draco=new DRACOLoader();draco.setDecoderPath('../vendor/');draco.setWorkerLimit(2);
  const loader=new GLTFLoader();loader.setDRACOLoader(draco);
  quality();setView('pool',true);controls.enabled=false;
  new ResizeObserver(resize).observe(stage);
  renderer.setAnimationLoop(()=>{
   if(document.hidden||mode!=='3d')return;
   if(transition){const t=Math.min(1,(performance.now()-transition.start)/900),s=t*t*(3-2*t);camera.position.lerpVectors(transition.from,transition.to,s);controls.target.lerpVectors(transition.fromTarget,transition.toTarget,s);if(t===1)transition=null;dirty=true;}
   controls.update();
   if(dirty||controls.autoRotate){renderer.render(scene,camera);dirty=false;frame++;stage.dataset.frames=String(frame);}
  });
  const gltf=await loader.loadAsync('./assets/foxiang.glb',ev=>{
   if(ev.total){const pct=Math.round(ev.loaded/ev.total*100);$('progress').value=pct;$('loadStatus').textContent=pct<100?`正在下载场景 · ${pct}%`:'正在解压模型与准备材质…';}
   else $('loadStatus').textContent=`正在下载场景 · ${(ev.loaded/1048576).toFixed(1)} MB`;
  });
  model=gltf.scene;prepareMaterials(model);scene.add(model);ready=true;stage.dataset.ready='true';
  $('loading').hidden=true;controls.enabled=mode==='3d';setStatus();quality();invalidate();draco.dispose();
 }catch(e){console.error(e);error('请检查网络与浏览器硬件加速，或先查看Blender 渲染图。');}
}
for(const b of document.querySelectorAll('[data-view]'))b.onclick=()=>setView(b.dataset.view);
for(const b of document.querySelectorAll('[data-mode]'))b.onclick=()=>setMode(b.dataset.mode);
$('reset').onclick=()=>setView('pool');
$('orbit').onchange=()=>{if(controls){transition=null;setMode('3d');controls.autoRotate=$('orbit').checked;invalidate();}};
$('wire').onchange=()=>{if(!model)return;model.traverse(o=>{if(o.isMesh)for(const m of Array.isArray(o.material)?o.material:[o.material])m.wireframe=$('wire').checked;});invalidate();};
$('exposure').oninput=()=>{const v=+$('exposure').value;$('exposureValue').value=v.toFixed(2);if(renderer)renderer.toneMappingExposure=v*.75;invalidate();};
$('quality').onchange=quality;
$('fullscreen').onclick=async()=>{try{if(document.fullscreenElement)await document.exitFullscreen();else if(stage.requestFullscreen)await stage.requestFullscreen();else status.textContent='此浏览器不支持全屏，请横屏浏览。';}catch{status.textContent='浏览器暂时无法进入全屏。';}};
document.addEventListener('fullscreenchange',()=>{$('fullscreen').textContent=document.fullscreenElement?'⛶ 退出全屏':'⛶ 全屏';resize();});
document.addEventListener('visibilitychange',invalidate);
canvas.addEventListener('keydown',e=>{
 if(!ready||mode!=='3d')return;
 if(e.key==='0'){e.preventDefault();setView('pool');return;}
 if(!['ArrowLeft','ArrowRight','ArrowUp','ArrowDown','+','=','-'].includes(e.key))return;
 e.preventDefault();transition=null;controls.autoRotate=false;$('orbit').checked=false;
 const s=new THREE.Spherical().setFromVector3(camera.position.clone().sub(controls.target));
 if(e.key==='ArrowLeft')s.theta+=.08;if(e.key==='ArrowRight')s.theta-=.08;
 if(e.key==='ArrowUp')s.phi-=.06;if(e.key==='ArrowDown')s.phi+=.06;
 if(e.key==='+'||e.key==='=')s.radius*=.90;if(e.key==='-')s.radius*=1.1;
 s.phi=THREE.MathUtils.clamp(s.phi,controls.minPolarAngle,controls.maxPolarAngle);s.radius=THREE.MathUtils.clamp(s.radius,controls.minDistance,controls.maxDistance);
 camera.position.copy(controls.target).add(new THREE.Vector3().setFromSpherical(s));controls.update();invalidate();
});
canvas.addEventListener('webglcontextlost',e=>{e.preventDefault();error('图形资源已暂停，请重新加载，或选择Blender 渲染图。');});
window.addEventListener('pagehide',()=>{renderer?.setAnimationLoop(null);});
window.addEventListener('pageshow',e=>{if(e.persisted)location.reload();});
init();
