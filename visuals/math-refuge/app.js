import * as THREE from 'three';
import {OrbitControls} from '../3d/vendor/OrbitControls.js';
import {EffectComposer} from './vendor/postprocessing/EffectComposer.js';
import {RenderPass} from './vendor/postprocessing/RenderPass.js';
import {UnrealBloomPass} from './vendor/postprocessing/UnrealBloomPass.js';
import {OutputPass} from './vendor/postprocessing/OutputPass.js';
import {createRetreat} from './scene.js?v=6-landscape';
import {createLecture} from './lecture.js?v=5-mobile';
import {createChalkReader} from './chalk-reader.js?v=5-mobile';
import {displayProfile,boardFraming} from './display-profile.js?v=5-mobile';
import {configureCameraInput} from './camera-input.js?v=4-controls';
import {SHOTS,smoothProgress,fadeAt,advanceShot} from './camera-paths.js?v=3-coast';

const $=id=>document.getElementById(id);
const reduced=matchMedia('(prefers-reduced-motion: reduce)');
let renderer,composer,camera,controls,cameraInput,retreat,bloom,lecture,reader,profile,nativeSamples=0;
let shot=0,time=0,lastTime=0,touring=!reduced.matches,free=false,blend=null,lightTimer;
const keys=new Set(),scene=new THREE.Scene();
const curves=SHOTS.map(s=>({
  position:new THREE.CatmullRomCurve3(s.positions.map(p=>new THREE.Vector3(...p))),
  target:new THREE.CatmullRomCurve3(s.targets.map(p=>new THREE.Vector3(...p)))
}));
const totalDuration=SHOTS.reduce((a,s)=>a+s.duration,0);
function fail(error){
  console.error(error);$('loading').hidden=true;$('error').hidden=false;
  $('errorText').textContent='请启用浏览器硬件加速后重试。若仍无法打开，请换用新版 Safari、Chrome 或 Edge。';
}
function updateLabels(){
  document.body.classList.toggle('teaching',Boolean(SHOTS[shot].lecture));
  reader?.chapter(Boolean(SHOTS[shot].lecture),$('lecturePanel').hidden);
  $('shotNumber').textContent=`0${shot+1} / ${SHOTS[shot].name}`;
  $('shotTitle').innerHTML=SHOTS[shot].title;
  $('shotDescription').textContent=SHOTS[shot].description;
  document.querySelectorAll('[data-shot]').forEach(b=>b.setAttribute('aria-current',String(Number(b.dataset.shot)===shot)));
  $('tour').textContent=touring?'暂停巡游':free?'恢复巡游':'继续巡游';
  $('tour').setAttribute('aria-pressed',String(touring));
  $('mode').textContent=touring?'自动镜头':free?'自由观察':'镜头已暂停';
}
function stopTour(){touring=false;free=true;blend=null;$('transition').style.opacity=0;updateLabels();}
function resumeTour(){
  touring=true;free=false;
  blend={elapsed:0,position:camera.position.clone(),target:controls.target.clone(),fov:camera.fov};
  updateLabels();
}
function applyShot(dt){
  const s=SHOTS[shot],fraction=time/s.duration,t=smoothProgress(fraction);
  const position=curves[shot].position.getPointAt(t),target=curves[shot].target.getPointAt(t);
  if(s.lecture&&lecture){
    // A steady board-height teaching camera follows the active pair, not a room orbit.
    const framing=boardFraming(camera.aspect,s.fov),focus=lecture.focus(framing.single);target.copy(focus);position.copy(focus).add(new THREE.Vector3(0,0,framing.distance));
    if(!blend&&dt>0){position.lerpVectors(camera.position,position,1-Math.exp(-dt*1.5));target.lerpVectors(controls.target,target,1-Math.exp(-dt*1.5));}
  }
  if(blend){
    blend.elapsed+=dt;const k=smoothProgress(Math.min(1,blend.elapsed/2));
    if(blend.position.distanceTo(position)>12){
      // Long jumps dissolve through black instead of flying through solid walls.
      camera.position.copy(k<.5?blend.position:position);controls.target.copy(k<.5?blend.target:target);
      camera.fov=k<.5?blend.fov:s.fov;$('transition').style.opacity=String(Math.sin(k*Math.PI));
    }else{
      camera.position.lerpVectors(blend.position,position,k);controls.target.lerpVectors(blend.target,target,k);
      camera.fov=THREE.MathUtils.lerp(blend.fov,s.fov,k);$('transition').style.opacity=0;
    }
    if(k===1)blend=null;
  }else{
    camera.position.copy(position);controls.target.copy(target);camera.fov=s.fov;
    $('transition').style.opacity=String(fadeAt(fraction)*.85);
  }
  camera.updateProjectionMatrix();controls.update();
  const prior=SHOTS.slice(0,shot).reduce((a,s)=>a+s.duration,0);
  $('timelineFill').style.width=`${100*(prior+time)/totalDuration}%`;
  $('world').dataset.shot=String(shot);$('world').dataset.mode=touring?'tour':'free';
}
function resize(){
  if(!renderer)return;
  profile=displayProfile(innerWidth,innerHeight,devicePixelRatio,$('quality').value,renderer.capabilities.maxSamples,nativeSamples);
  camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();
  renderer.setPixelRatio(profile.pixelRatio);renderer.setSize(innerWidth,innerHeight);
  if(composer){
    // Dispose on sample-count changes: changing .samples alone does not rebuild
    // an already allocated WebGL framebuffer at the same dimensions.
    for(const target of [composer.renderTarget1,composer.renderTarget2])if(target.samples!==profile.samples){target.samples=profile.samples;target.dispose();}
    composer.setPixelRatio(profile.direct?1:profile.pixelRatio);composer.setSize(innerWidth,innerHeight);
    bloom.enabled=profile.bloom;
  }
  renderer.shadowMap.enabled=profile.shadows;renderer.shadowMap.needsUpdate=true;
  if(retreat&&retreat.sun.shadow.mapSize.x!==profile.shadowSize){retreat.sun.shadow.mapSize.set(profile.shadowSize,profile.shadowSize);retreat.sun.shadow.map?.dispose();retreat.sun.shadow.map=null;}
  $('qualityReadout').textContent=`${profile.pixelRatio.toFixed(2)}× 分辨率 · ${profile.direct?nativeSamples:profile.samples}× 抗锯齿`;
  $('world').dataset.pixelRatio=String(profile.pixelRatio);$('world').dataset.antialias=String(profile.direct?nativeSamples:profile.samples);
}
function setQuality(){
  resize();
}
function tick(stamp){
  const dt=Math.min(.05,(stamp-lastTime)/1000||0);lastTime=stamp;
  if(document.hidden)return;
  if(touring){
    if(!blend){const state=advanceShot(shot,time,dt,Number($('speed').value));if(shot!==state.index){shot=state.index;updateLabels();}time=state.time;}
    applyShot(dt);
  }else{
    const forward=new THREE.Vector3();camera.getWorldDirection(forward);forward.y=0;forward.normalize();
    const right=new THREE.Vector3().crossVectors(forward,new THREE.Vector3(0,1,0));
    const move=new THREE.Vector3();
    if(keys.has('w')||keys.has('arrowup'))move.add(forward);
    if(keys.has('s')||keys.has('arrowdown'))move.sub(forward);
    if(keys.has('a')||keys.has('arrowleft'))move.sub(right);
    if(keys.has('d')||keys.has('arrowright'))move.add(right);
    if(keys.has('q'))move.y-=1;if(keys.has('e'))move.y+=1;
    if(move.lengthSq()){move.normalize().multiplyScalar(dt*(keys.has('shift')?10:4));camera.position.add(move);controls.target.add(move);}
    // Keep free-flight away from the clipping plane and terrain basement.
    const oldY=camera.position.y;camera.position.y=Math.max(-.8,camera.position.y);controls.target.y+=camera.position.y-oldY;
    controls.update();
  }
  if(!reduced.matches){retreat.water.material.uniforms.time.value+=dt*.35;retreat.ocean.material.uniforms.time.value+=dt;retreat.landscape.update(dt);}
  if(lecture){lecture.update(dt,reduced.matches);updateLectureUI();reader?.update();}
  if(profile.direct)renderer.render(scene,camera);else composer.render();
}
try{
  renderer=new THREE.WebGLRenderer({canvas:$('world'),antialias:true,powerPreference:'high-performance'});
  nativeSamples=renderer.getContext().getParameter(renderer.getContext().SAMPLES);
  renderer.outputColorSpace=THREE.SRGBColorSpace;renderer.toneMapping=THREE.ACESFilmicToneMapping;renderer.toneMappingExposure=.9;
  renderer.shadowMap.enabled=true;renderer.shadowMap.type=THREE.PCFSoftShadowMap;
  renderer.shadowMap.autoUpdate=false;renderer.shadowMap.needsUpdate=true;
  camera=new THREE.PerspectiveCamera(49,innerWidth/innerHeight,.08,12000);
  controls=new OrbitControls(camera,$('world'));cameraInput=configureCameraInput(controls,$('world'));
  controls.minDistance=.4;controls.maxDistance=200;controls.maxPolarAngle=Math.PI*.94;controls.enablePan=true;
  controls.addEventListener('start',()=>{stopTour();});
  camera.position.fromArray(SHOTS[0].positions[0]);controls.target.fromArray(SHOTS[0].targets[0]);controls.update();
  resize();
  retreat=await createRetreat(renderer,scene,text=>{$('loadMessage').textContent=text;});
  $('loadMessage').textContent='正在安装六块升降黑板与谱序列板书…';
  lecture=await createLecture(scene,renderer);
  reader=createChalkReader(lecture);
  for(const [i,page] of lecture.pages.entries()){
    const option=document.createElement('option');option.value=String(i);option.textContent=`${i+1}. ${page.source} · ${page.title}`;$('lecturePage').append(option);
  }
  if(reduced.matches){lecture.playing=false;lecture.staticPage();}
  composer=new EffectComposer(renderer);composer.addPass(new RenderPass(scene,camera));
  bloom=new UnrealBloomPass(new THREE.Vector2(innerWidth,innerHeight),.18,.4,1.1);composer.addPass(bloom);composer.addPass(new OutputPass());
  setQuality();updateLabels();time=.85;applyShot(0);$('transition').style.opacity=0;
  // Shader compilation failures are reported, not hidden behind an endless loader.
  renderer.debug.onShaderError=()=>fail(new Error('The scene shader could not compile'));
  await renderer.compileAsync(scene,camera);
  $('loading').hidden=true;$('world').dataset.ready='true';
  renderer.setAnimationLoop(tick);
}catch(error){fail(error);}

$('tour').addEventListener('click',()=>{
  if(!renderer||!retreat)return;
  if(touring){touring=false;$('transition').style.opacity=0;updateLabels();}else resumeTour();
});
document.querySelectorAll('[data-shot]').forEach(button=>button.addEventListener('click',()=>{
  if(!retreat)return;shot=Number(button.dataset.shot);time=.85;
  if(reduced.matches){touring=false;free=false;blend=null;applyShot(0);$('transition').style.opacity=0;updateLabels();}
  else resumeTour();
}));
$('settingsButton').addEventListener('click',()=>{
  $('settings').hidden=!$('settings').hidden;$('settingsButton').setAttribute('aria-expanded',String(!$('settings').hidden));
});
$('quality').addEventListener('change',()=>{if(retreat)setQuality();});
$('rotationSensitivity').addEventListener('input',event=>cameraInput?.set(event.target.value));
$('light').addEventListener('input',()=>{
  if(!retreat)return;retreat.lighting(Number($('light').value));renderer.shadowMap.needsUpdate=true;clearTimeout(lightTimer);
  lightTimer=setTimeout(()=>retreat.lighting(Number($('light').value),true),180);
});
$('fullscreen').addEventListener('click',async()=>{
  try{
    if(document.fullscreenElement||document.webkitFullscreenElement){
      const exit=document.exitFullscreen||document.webkitExitFullscreen;if(exit)await exit.call(document);
    }else{
      const enter=document.documentElement.requestFullscreen||document.documentElement.webkitRequestFullscreen;
      if(enter)await enter.call(document.documentElement);else $('fullscreen').textContent='请使用浏览器全屏';
    }
  }catch{$('fullscreen').textContent='全屏未获允许，请重试';}
});
function syncFullscreen(){const active=Boolean(document.fullscreenElement||document.webkitFullscreenElement);$('fullscreen').textContent=active?'退出全屏':'全屏浏览';$('fullscreen').setAttribute('aria-pressed',String(active));}
document.addEventListener('fullscreenchange',syncFullscreen);document.addEventListener('webkitfullscreenchange',syncFullscreen);
function immersive(hide){document.body.classList.toggle('immersive',hide);$('showUI').hidden=!hide;if(hide){$('settings').hidden=true;$('settingsButton').setAttribute('aria-expanded','false');}}
$('hideUI').addEventListener('click',()=>immersive(true));$('showUI').addEventListener('click',()=>immersive(false));
window.addEventListener('keydown',event=>{
  if(/INPUT|SELECT|TEXTAREA/.test(event.target.tagName))return;
  const key=event.key.toLowerCase();
  if(key==='h'){immersive(!document.body.classList.contains('immersive'));return;}
  if(key==='escape'){immersive(false);$('settings').hidden=true;$('settingsButton').setAttribute('aria-expanded','false');$('lecturePanel').hidden=true;$('lectureButton').setAttribute('aria-expanded','false');reader?.close();return;}
  if(event.target.closest('#chalkReader,#lecturePanel,#settings'))return;
  if(key===' ' && event.target.tagName!=='BUTTON'){event.preventDefault();$('tour').click();return;}
  if(['w','a','s','d','q','e','arrowup','arrowdown','arrowleft','arrowright','shift'].includes(key)){
    event.preventDefault();stopTour();keys.add(key);
  }
});
window.addEventListener('keyup',event=>keys.delete(event.key.toLowerCase()));window.addEventListener('blur',()=>keys.clear());
document.addEventListener('visibilitychange',()=>{keys.clear();lastTime=performance.now();});
window.addEventListener('resize',resize);
reduced.addEventListener('change',()=>{if(reduced.matches){touring=false;if(lecture){lecture.playing=false;lecture.staticPage();}updateLabels();}});
$('world').addEventListener('webglcontextlost',event=>{event.preventDefault();renderer?.setAnimationLoop(null);fail(new Error('WebGL context lost'));});
window.addEventListener('pagehide',()=>renderer?.setAnimationLoop(null));
window.addEventListener('pageshow',event=>{if(event.persisted&&retreat){lastTime=performance.now();renderer.setAnimationLoop(tick);}});

let lectureStatus='';
function updateLectureUI(){
  const status=lecture.status();if(status!==lectureStatus){$('lectureStatus').textContent=status;lectureStatus=status;}
  $('lecturePlay').textContent=lecture.playing?'暂停板书':'继续板书';$('lecturePlay').setAttribute('aria-pressed',String(lecture.playing));
  if(document.activeElement!==$('lecturePage'))$('lecturePage').value=String(lecture.clock.page);
  lecture.heights().forEach((value,i)=>{const slider=$('boardLift'+i);if(document.activeElement!==slider)slider.value=String(value);});
}
function focusLecture(){
  if(!lecture)return;shot=SHOTS.findIndex(s=>s.lecture);time=.85;
  if(reduced.matches){const framing=boardFraming(camera.aspect,SHOTS[shot].fov),focus=lecture.focus(framing.single);free=false;touring=false;blend=null;camera.fov=SHOTS[shot].fov;camera.updateProjectionMatrix();camera.position.copy(focus).add(new THREE.Vector3(0,0,framing.distance));controls.target.copy(focus);controls.update();updateLabels();}
  else resumeTour();
}
$('lectureButton').addEventListener('click',()=>{
  if(!lecture)return;reader?.close();$('lecturePanel').hidden=!$('lecturePanel').hidden;$('lectureButton').setAttribute('aria-expanded',String(!$('lecturePanel').hidden));if(!$('lecturePanel').hidden)focusLecture();
});
$('lectureClose').addEventListener('click',()=>{$('lecturePanel').hidden=true;$('lectureButton').setAttribute('aria-expanded','false');});
$('lectureFocus').addEventListener('click',focusLecture);
$('lecturePlay').addEventListener('click',()=>{if(!lecture)return;lecture.playing=!lecture.playing;if(reduced.matches)lecture.staticPage();});
for(const [id,delta] of [['lecturePrevious',-1],['lectureNext',1]])$(id).addEventListener('click',()=>{if(!lecture)return;lecture.step(delta);if(reduced.matches||!lecture.playing)lecture.staticPage();});
$('lectureRewrite').addEventListener('click',()=>{if(!lecture)return;lecture.rewrite();if(reduced.matches)lecture.staticPage();else lecture.playing=true;});
$('lecturePage').addEventListener('change',event=>{if(!lecture)return;lecture.select(Number(event.target.value));if(reduced.matches||!lecture.playing)lecture.staticPage();});
for(let pair=0;pair<3;pair++){
  $('boardLift'+pair).addEventListener('input',event=>{if(!lecture)return;lecture.playing=false;lecture.lift(pair,event.target.value);});
  $('boardSwap'+pair).addEventListener('click',()=>{if(!lecture)return;lecture.playing=false;lecture.lift(pair,1-lecture.heights()[pair]);});
}
