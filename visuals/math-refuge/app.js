import * as THREE from 'three';
import {controlLabel} from './control-label.js?v=20-slower-tour';
import {OrbitControls} from '../3d/vendor/OrbitControls.js';
import {EffectComposer} from './vendor/postprocessing/EffectComposer.js';
import {RenderPass} from './vendor/postprocessing/RenderPass.js';
import {UnrealBloomPass} from './vendor/postprocessing/UnrealBloomPass.js';
import {OutputPass} from './vendor/postprocessing/OutputPass.js';
import {createRetreat} from './scene.js?v=20-slower-tour';
import {createLecture} from './lecture.js?v=21-language-columns';
import {configureLectureRoot,lectureViewOffset,BUILDING_SCALE} from './site-layout.js?v=20-slower-tour';
import {seaLevel} from './landscape-shape.js?v=20-slower-tour';
import {createChalkReader} from './chalk-reader.js?v=20-slower-tour';
import {displayProfile,boardFraming} from './display-profile.js?v=5-mobile';
import {configureCameraInput} from './camera-input.js?v=4-controls';
import {bindCameraIntent} from './camera-intent.js?v=8-manual';
import {SHOTS,smoothProgress,advanceShot,OPENING_OVERVIEW_MS,transitionSeconds} from './camera-paths.js?v=20-slower-tour';
import {BoardFollow} from './board-follow.js?v=20-slower-tour';
import {RetreatTime} from './retreat-time.js?v=20-slower-tour';
import {constrainAboveWater} from './camera-bounds.js?v=20-slower-tour';
import {bindPhysicalButtons} from './physical-buttons.js?v=20-slower-tour';
const sceneTime=new RetreatTime(),boardFollow=new BoardFollow();let lastSunUpdate=-1,lastEnvironmentHour=-1;

const $=id=>document.getElementById(id);
const reduced=matchMedia('(prefers-reduced-motion: reduce)');
let renderer,composer,camera,controls,cameraInput,cameraIntent,retreat,bloom,lecture,reader,profile,nativeSamples=0;
let shot=SHOTS.findIndex(s=>s.name==='远眺'),time=SHOTS[shot].duration*.62,lastTime=0,touring=false,free=false,blend=null,lightTimer,opening={started:null};
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
  $('shotNumber').textContent=opening?'总览':`0${shot+1} / ${SHOTS[shot].name}`;
  $('shotTitle').innerHTML=SHOTS[shot].title;
  $('shotDescription').textContent=SHOTS[shot].description;
  document.querySelectorAll('[data-shot]').forEach(b=>b.setAttribute('aria-current',String(Number(b.dataset.shot)===shot)));
  controlLabel($('tour'),touring?'暂停巡游':free?'恢复巡游':'继续巡游');
  $('tour').setAttribute('aria-pressed',String(touring));
  $('mode').textContent=opening?'总览 · 5 秒后进入板书':SHOTS[shot].lecture?'跟随当前板书':touring?'自动镜头':free?'自由观察':'镜头已暂停';
  $('world').dataset.mode=touring?'tour':free?'free':'paused';
}
function stopTour(){
  opening=null;
  if(SHOTS[shot].lecture)boardFollow.touch();
  const changed=touring||!free||blend;
  touring=false;free=true;blend=null;$('transition').style.opacity=0;
  if(changed)updateLabels();
}
function beginTransition(){
  const position=camera.position.clone(),target=controls.target.clone(),damping=controls.enableDamping;
  controls.enableDamping=false;controls.update();camera.position.copy(position);controls.target.copy(target);controls.update();controls.enableDamping=damping;
  blend={elapsed:0,position,target,fov:camera.fov,duration:reduced.matches?1.6:transitionSeconds(position.distanceTo(curves[shot].position.getPointAt(smoothProgress(time/SHOTS[shot].duration))))};
  $('transition').style.opacity=0;
}
function selectShot(index){
  opening=null;shot=index;time=.85;boardFollow.reset();touring=false;free=false;
  beginTransition();updateLabels();
}
function resumeTour(){
  opening=null;boardFollow.reset();touring=true;free=false;
  beginTransition();updateLabels();
}
function applyShot(dt){
  const s=SHOTS[shot],fraction=time/s.duration,t=smoothProgress(fraction);
  const position=curves[shot].position.getPointAt(t),target=curves[shot].target.getPointAt(t);
  if(s.lecture&&lecture){
    // A steady board-height teaching camera follows the active pair, not a room orbit.
    const framing=boardFraming(camera.aspect,s.fov),focus=lecture.focus(true);target.copy(focus);position.copy(focus).add(new THREE.Vector3(...lectureViewOffset(framing.distance)));
    if(!blend&&dt>0){position.lerpVectors(camera.position,position,1-Math.exp(-dt*.75));target.lerpVectors(controls.target,target,1-Math.exp(-dt*.75));}
  }
  if(blend){
    blend.elapsed+=dt;const k=smoothProgress(Math.min(1,blend.elapsed/blend.duration));
    camera.position.lerpVectors(blend.position,position,k);controls.target.lerpVectors(blend.target,target,k);
    camera.fov=THREE.MathUtils.lerp(blend.fov,s.fov,k);$('transition').style.opacity=0;
    if(k===1)blend=null;
  }else{
    camera.position.copy(position);controls.target.copy(target);camera.fov=s.fov;
    $('transition').style.opacity=0;
  }
  camera.updateProjectionMatrix();controls.update();
  const prior=SHOTS.slice(0,shot).reduce((a,s)=>a+s.duration,0);
  $('timelineFill').style.width=`${100*(prior+time)/totalDuration}%`;
  $('world').dataset.shot=String(shot);$('world').dataset.mode=touring?'tour':free?'free':'paused';
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
    bloom.enabled=false; // Chalk and stone must never acquire a screen-space halo.
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
  if(lecture){lecture.update(dt,reduced.matches);updateLectureUI();reader?.update();}
  if(opening){
    if(opening.started===null)opening.started=stamp;
    if(stamp-opening.started>=OPENING_OVERVIEW_MS)selectShot(0);
  }
  if(touring){
    if(!blend){const state=advanceShot(shot,time,dt,Number($('speed').value));time=state.time;if(shot!==state.index){shot=state.index;beginTransition();updateLabels();}}
    applyShot(dt);
  }else if(blend){
    applyShot(dt);
  }else if(SHOTS[shot].lecture&&lecture&&boardFollow.following){
    // Board tracking belongs to the teaching chapter, independently of touring.
    applyShot(reduced.matches?0:dt);
  }else{
    const forward=new THREE.Vector3();camera.getWorldDirection(forward);forward.y=0;forward.normalize();
    const right=new THREE.Vector3().crossVectors(forward,new THREE.Vector3(0,1,0));
    const move=new THREE.Vector3();
    if(keys.has('w')||keys.has('arrowup'))move.add(forward);
    if(keys.has('s')||keys.has('arrowdown'))move.sub(forward);
    if(keys.has('a')||keys.has('arrowleft'))move.sub(right);
    if(keys.has('d')||keys.has('arrowright'))move.add(right);
    if(keys.has('q'))move.y-=1;if(keys.has('e'))move.y+=1;
    if(move.lengthSq()){if(SHOTS[shot].lecture)boardFollow.touch();move.normalize().multiplyScalar(dt*(keys.has('shift')?10:4));camera.position.add(move);controls.target.add(move);}
    // Keep free-flight away from the clipping plane and terrain basement.
    controls.update();
  }
  if(SHOTS[shot].lecture&&lecture){
    $('mode').textContent=boardFollow.following?'跟随当前板书':`自由观察 · ${Math.ceil(boardFollow.remaining)} 秒后跟随`;
    $('world').dataset.boardFollow=boardFollow.following?'following':'manual';
    $('world').dataset.board=String(lecture.clock.active);
    $('world').dataset.camera=camera.position.toArray().map(x=>x.toFixed(3)).join(',');
  }else delete $('world').dataset.boardFollow;
  $('world').dataset.camera=camera.position.toArray().map(x=>x.toFixed(3)).join(',');
  $('world').dataset.transition=blend?'moving':'settled';$('world').dataset.opening=opening?'overview':'complete';
  constrainAboveWater(camera,controls.target,seaLevel*BUILDING_SCALE);
  if(!reduced.matches){retreat.ocean.material.uniforms.time.value+=dt;retreat.landscape.update(dt);}
  updateSceneTime(dt);
  if(profile.direct)renderer.render(scene,camera);else composer.render();
}
try{
  renderer=new THREE.WebGLRenderer({canvas:$('world'),antialias:true,powerPreference:'high-performance'});
  nativeSamples=renderer.getContext().getParameter(renderer.getContext().SAMPLES);
  renderer.outputColorSpace=THREE.SRGBColorSpace;renderer.toneMapping=THREE.ACESFilmicToneMapping;renderer.toneMappingExposure=.78;
  renderer.shadowMap.enabled=true;renderer.shadowMap.type=THREE.PCFSoftShadowMap;
  renderer.shadowMap.autoUpdate=false;renderer.shadowMap.needsUpdate=true;
  camera=new THREE.PerspectiveCamera(49,innerWidth/innerHeight,.2,12000);
  controls=new OrbitControls(camera,$('world'));cameraInput=configureCameraInput(controls,$('world'));
  cameraIntent=bindCameraIntent(document,$('world'),stopTour);
  controls.minDistance=.4;controls.maxDistance=200;controls.maxPolarAngle=Math.PI*.94;controls.enablePan=true;
  controls.addEventListener('change',()=>constrainAboveWater(camera,controls.target,seaLevel*BUILDING_SCALE));
  controls.autoRotate=false;
  controls.addEventListener('start',()=>{stopTour();if(SHOTS[shot].lecture)boardFollow.begin();});
  controls.addEventListener('end',()=>{if(SHOTS[shot].lecture)boardFollow.end();});
  window.addEventListener('blur',()=>{if(boardFollow.interacting)boardFollow.end();});
  $('world').addEventListener('pointercancel',()=>{if(boardFollow.interacting)boardFollow.end();});
  camera.position.copy(curves[shot].position.getPointAt(smoothProgress(time/SHOTS[shot].duration)));controls.target.copy(curves[shot].target.getPointAt(smoothProgress(time/SHOTS[shot].duration)));controls.update();
  resize();
  retreat=await createRetreat(renderer,scene,text=>{$('loadMessage').textContent=text;});
  $('loadMessage').textContent='正在安装六块升降黑板与谱序列板书…';
  const lectureRoot=new THREE.Group();lectureRoot.name='East-facing compact auditorium blackboards';configureLectureRoot(lectureRoot);scene.add(lectureRoot);
  lecture=await createLecture(lectureRoot,renderer);retreat.roomFill.apply(lectureRoot);
  reader=createChalkReader(lecture);
  installPhysicalControls();
  for(const [i,page] of lecture.pages.entries()){
    const option=document.createElement('option');option.value=String(i);option.textContent=`${page.source} · ${page.title}`;$('lecturePage').append(option);
  }
  if(reduced.matches){lecture.playing=false;lecture.staticPage();}
  composer=new EffectComposer(renderer);composer.addPass(new RenderPass(scene,camera));
  bloom=new UnrealBloomPass(new THREE.Vector2(innerWidth,innerHeight),0,.25,1.6);bloom.enabled=false;composer.addPass(bloom);composer.addPass(new OutputPass());
  setQuality();updateSceneTime();updateLabels();applyShot(0);$('transition').style.opacity=0;
  // Shader compilation failures are reported, not hidden behind an endless loader.
  renderer.debug.onShaderError=()=>fail(new Error('The scene shader could not compile'));
  await renderer.compileAsync(scene,camera);
  $('loading').hidden=true;$('world').dataset.ready='true';
  renderer.setAnimationLoop(tick);
}catch(error){fail(error);}

$('tour').addEventListener('click',()=>{
  if(!renderer||!retreat||!cameraIntent.canActivate())return;
  if(touring){opening=null;touring=false;blend=null;$('transition').style.opacity=0;updateLabels();}else resumeTour();
});
document.querySelectorAll('[data-shot]').forEach(button=>button.addEventListener('click',()=>{
  if(!retreat||!cameraIntent.canActivate())return;selectShot(Number(button.dataset.shot));
}));
$('settingsButton').addEventListener('click',()=>{
  $('settings').hidden=!$('settings').hidden;$('settingsButton').setAttribute('aria-expanded',String(!$('settings').hidden));
});
$('quality').addEventListener('change',()=>{if(retreat)setQuality();});
$('boardFollowDelay').addEventListener('input',event=>{boardFollow.setDelay(event.target.value);$('boardFollowDelayValue').textContent=boardFollow.delay+' 秒';});
$('writingSpeed').addEventListener('input',event=>{const value=Number(event.target.value);lecture?.setWritingSpeed(value);$('writingSpeedValue').textContent=value+' ×';});
$('rotationSensitivity').addEventListener('input',event=>cameraInput?.set(event.target.value));
$('light').addEventListener('input',()=>{
  if(!retreat)return;sceneTime.previewAt(Number($('light').value));lastSunUpdate=-1;clearTimeout(lightTimer);
  lightTimer=setTimeout(()=>{retreat.setTime(sceneTime.hour,true);lastEnvironmentHour=sceneTime.hour;},180);
});
$('clockPlay').addEventListener('click',()=>{clearTimeout(lightTimer);sceneTime.sync();lastSunUpdate=-1;updateSceneTime();});
function updateSceneTime(){
  sceneTime.update();
  if(lastSunUpdate<0||Math.abs(sceneTime.hour-lastSunUpdate)>.01){
    const regenerate=lastEnvironmentHour<0||Math.abs(sceneTime.hour-lastEnvironmentHour)>.5;
    retreat.setTime(sceneTime.hour,regenerate);lastSunUpdate=sceneTime.hour;if(regenerate)lastEnvironmentHour=sceneTime.hour;
    renderer.shadowMap.needsUpdate=true;
  }
  if(document.activeElement!==$('light'))$('light').value=String(sceneTime.hour);
  const minutes=Math.floor(sceneTime.hour*60);
  $('sceneClock').textContent=String(Math.floor(minutes/60)).padStart(2,'0')+':'+String(minutes%60).padStart(2,'0');
  controlLabel($('clockPlay'),sceneTime.preview?'回到当前时间':'已同步当前时间');
  $('clockPlay').setAttribute('aria-pressed',String(!sceneTime.preview));
  $('world').dataset.clockMode=sceneTime.preview?'preview':'local';
  $('world').dataset.hour=sceneTime.hour.toFixed(4);
  lecture?.setConsoleState();
}

let changingLanguage=false;
async function switchChalkLanguage(){
  if(!lecture||changingLanguage)return;changingLanguage=true;
  try{await lecture.setLanguage(lecture.language==='zh'?'en':'zh');
    for(const [i,option] of [...$('lecturePage').options].entries()){const copy=lecture.copy(i);option.textContent=`${copy.source} · ${copy.title}`;}reader?.update();
  }catch(error){$('lectureStatus').textContent=error.message;}finally{changingLanguage=false;}
}
function installPhysicalControls(){
  const ray=new THREE.Raycaster(),pointer=new THREE.Vector2();
  const hit=e=>{
    const rect=$('world').getBoundingClientRect();pointer.set((e.clientX-rect.left)/rect.width*2-1,1-(e.clientY-rect.top)/rect.height*2);
    scene.updateMatrixWorld(true);camera.updateMatrixWorld(true);ray.setFromCamera(pointer,camera);
    const candidate=ray.intersectObjects(lecture.consoleButtons,false)[0];if(!candidate||candidate.distance>15)return null;
    // Ignore transparent glazing, but opaque roof/walls must block a press.
    for(const h of ray.intersectObjects(scene.children,true)){
      if(h.distance>=candidate.distance-.015)break;
      let visible=true;for(let p=h.object;p;p=p.parent)if(!p.visible)visible=false;
      if(!visible||h.object.parent===candidate.object||h.object===candidate.object)continue;
      const material=h.object.material;if(material?.transparent&&material.opacity<.5)continue;
      if(h.object.isMesh)return null;
    }
    return candidate.object;
  };
  bindPhysicalButtons($('world'),controls,hit,action=>{
    if(action==='language')switchChalkLanguage();
  });
}
$('fullscreen').addEventListener('click',async()=>{
  try{
    if(document.fullscreenElement||document.webkitFullscreenElement){
      const exit=document.exitFullscreen||document.webkitExitFullscreen;if(exit)await exit.call(document);
    }else{
      const enter=document.documentElement.requestFullscreen||document.documentElement.webkitRequestFullscreen;
      if(enter)await enter.call(document.documentElement);else controlLabel($('fullscreen'),'请使用浏览器全屏');
    }
  }catch{controlLabel($('fullscreen'),'全屏未获允许，请重试');}
});
function syncFullscreen(){const active=Boolean(document.fullscreenElement||document.webkitFullscreenElement);controlLabel($('fullscreen'),active?'退出全屏':'全屏浏览');$('fullscreen').setAttribute('aria-pressed',String(active));}
document.addEventListener('fullscreenchange',syncFullscreen);document.addEventListener('webkitfullscreenchange',syncFullscreen);
function immersive(hide){document.body.classList.toggle('immersive',hide);$('showUI').hidden=!hide;if(hide){$('settings').hidden=true;$('settingsButton').setAttribute('aria-expanded','false');}}
$('hideUI').addEventListener('click',()=>immersive(true));$('showUI').addEventListener('click',()=>immersive(false));
window.addEventListener('keydown',event=>{
  if(/INPUT|SELECT|TEXTAREA/.test(event.target.tagName))return;
  const key=event.key.toLowerCase();
  if(key==='h'){immersive(!document.body.classList.contains('immersive'));return;}
  if(key==='escape'){immersive(false);$('settings').hidden=true;$('settingsButton').setAttribute('aria-expanded','false');$('lecturePanel').hidden=true;$('lectureButton').setAttribute('aria-expanded','false');reader?.close();return;}
  if(event.target.closest('#chalkReader,#lecturePanel,#settings'))return;
  if(key===' ' && event.target.tagName!=='BUTTON'){event.preventDefault();if(!event.repeat&&cameraIntent?.canActivate())$('tour').click();return;}
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
  controlLabel($('lecturePlay'),lecture.playing?'暂停板书':'继续板书');$('lecturePlay').setAttribute('aria-pressed',String(lecture.playing));
  if(document.activeElement!==$('lecturePage'))$('lecturePage').value=String(lecture.clock.page);
  lecture.heights().forEach((value,i)=>{const slider=$('boardLift'+i);if(document.activeElement!==slider)slider.value=String(value);});
}
function focusLecture(){
  if(!lecture||!cameraIntent.canActivate())return;
  selectShot(0);
}
$('lectureButton').addEventListener('click',()=>{
  if(!lecture)return;reader?.close();$('lecturePanel').hidden=!$('lecturePanel').hidden;$('lectureButton').setAttribute('aria-expanded',String(!$('lecturePanel').hidden));if(!$('lecturePanel').hidden)focusLecture();
});
$('lectureClose').addEventListener('click',()=>{$('lecturePanel').hidden=true;$('lectureButton').setAttribute('aria-expanded','false');});
$('lectureFocus').addEventListener('click',focusLecture);
let teachingShade=false;
$('lectureShade').addEventListener('click',()=>{
  if(!retreat)return;teachingShade=!teachingShade;retreat.campus.setTeachingShade(teachingShade);
  $('lectureShade').setAttribute('aria-pressed',String(teachingShade));controlLabel($('lectureShade'),teachingShade?'收起遮光帘':'放下海景遮光帘');renderer.shadowMap.needsUpdate=true;
});
$('lecturePlay').addEventListener('click',()=>{if(!lecture)return;lecture.playing=!lecture.playing;if(reduced.matches)lecture.staticPage();});
for(const [id,delta] of [['lecturePrevious',-1],['lectureNext',1]])$(id).addEventListener('click',()=>{if(!lecture)return;lecture.step(delta);if(reduced.matches||!lecture.playing)lecture.staticPage();});
$('lectureRewrite').addEventListener('click',()=>{if(!lecture)return;lecture.rewrite();if(reduced.matches)lecture.staticPage();else lecture.playing=true;});
$('lecturePage').addEventListener('change',event=>{if(!lecture)return;lecture.select(Number(event.target.value));if(reduced.matches||!lecture.playing)lecture.staticPage();});
for(let pair=0;pair<3;pair++){
  $('boardLift'+pair).addEventListener('input',event=>{if(!lecture)return;lecture.playing=false;lecture.lift(pair,event.target.value);});
  $('boardSwap'+pair).addEventListener('click',()=>{if(!lecture)return;lecture.playing=false;lecture.lift(pair,1-lecture.heights()[pair]);});
}
