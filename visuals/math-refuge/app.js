import * as THREE from 'three';
import {createBackgroundMusic} from './background-music.js?v=25-music';
import {controlLabel} from './control-label.js?v=22-handwritten-cover';
import {OrbitControls} from '../3d/vendor/OrbitControls.js';
import {EffectComposer} from './vendor/postprocessing/EffectComposer.js';
import {RenderPass} from './vendor/postprocessing/RenderPass.js';
import {UnrealBloomPass} from './vendor/postprocessing/UnrealBloomPass.js';
import {OutputPass} from './vendor/postprocessing/OutputPass.js';
import {createRetreat} from './scene.js?v=37-speaker';
import {createLecture} from './lecture.js?v=36-board-detail';
import {configureLectureRoot,lectureViewOffset,BUILDING_SCALE} from './site-layout.js?v=36-board-detail';
import {seaLevel} from './landscape-shape.js?v=36-board-detail';
import {createChalkReader} from './chalk-reader.js?v=32-report-position';
import {displayProfile,boardFraming} from './display-profile.js?v=24-smooth-motion';
import {configureCameraInput} from './camera-input.js?v=4-controls';
import {bindCameraIntent} from './camera-intent.js?v=8-manual';
import {SHOTS,smoothProgress,advanceShot,OPENING_OVERVIEW_MS,transitionSeconds} from './camera-paths.js?v=37-speaker';
import {BoardFollow} from './board-follow.js?v=22-handwritten-cover';
import {RetreatTime} from './retreat-time.js?v=22-handwritten-cover';
import {constrainAboveWater} from './camera-bounds.js?v=22-handwritten-cover';
import {bindPhysicalButtons} from './physical-buttons.js?v=36-board-detail';
import {motionCoordinate} from './camera-motion.js';
const sceneTime=new RetreatTime(),boardFollow=new BoardFollow();let lastSunUpdate=-1,lastEnvironmentHour=-1;

const $=id=>document.getElementById(id);
const backgroundMusic=createBackgroundMusic({audio:$('backgroundMusic'),button:$('musicButton'),volume:$('musicVolume'),readout:$('musicVolumeValue')});
let entered=false;
$('enterButton').addEventListener('click',()=>{
  if(entered||$('world').dataset.ready!=='true')return;
  entered=true;lastTime=performance.now();$('loading').hidden=true;$('world').dataset.entered='true';
  backgroundMusic.start();$('world').focus({preventScroll:true});
});
const reduced=matchMedia('(prefers-reduced-motion: reduce)');
let renderer,composer,camera,controls,cameraInput,cameraIntent,retreat,bloom,lecture,reader,profile,nativeSamples=0;
let shot=SHOTS.findIndex(s=>s.name==='远眺'),time=SHOTS[shot].duration*.62,lastTime=0,touring=false,free=false,blend=null,lightTimer,opening={started:null};
const keys=new Set(),scene=new THREE.Scene();
const curves=SHOTS.map(s=>({
  position:new THREE.CatmullRomCurve3(s.positions.map(p=>new THREE.Vector3(...p))),
  target:new THREE.CatmullRomCurve3(s.targets.map(p=>new THREE.Vector3(...p)))
}));
const totalDuration=SHOTS.reduce((a,s)=>a+s.duration,0);
const motionVelocity=new THREE.Vector3(),motionAcceleration=new THREE.Vector3(),previousPosition=new THREE.Vector3(),previousVelocity=new THREE.Vector3();
const shotPosition=new THREE.Vector3(),shotTarget=new THREE.Vector3(),viewDirection=new THREE.Vector3(),lookMatrix=new THREE.Matrix4(),viewUp=new THREE.Vector3(0,1,0);
let motionSample=false,lastUIStamp=0,choosingReport=false,speakerView=false;
function shotPose(){
  if(speakerView){const pose=retreat.campus.lectern.speakerPose();shotPosition.copy(pose.position);shotTarget.copy(pose.target);return;}
  const s=SHOTS[shot],t=smoothProgress(time/s.duration);
  curves[shot].position.getPointAt(t,shotPosition);curves[shot].target.getPointAt(t,shotTarget);
  if(s.lecture&&lecture){
    const framing=boardFraming(camera.aspect,s.fov);shotTarget.copy(choosingReport?lecture.reportFocus():lecture.focus(true));
    shotPosition.copy(shotTarget).add(viewDirection.fromArray(lectureViewOffset(choosingReport?Math.max(4.6,framing.distance):framing.distance)));
  }
}
function fail(error){
  console.error(error);$('loading').hidden=true;$('error').hidden=false;
  $('errorText').textContent='请启用浏览器硬件加速后重试。若仍无法打开，请换用新版 Safari、Chrome 或 Edge。';
}
function updateLabels(){
  document.body.classList.toggle('teaching',Boolean(SHOTS[shot].lecture&&!speakerView));
  reader?.chapter(Boolean(SHOTS[shot].lecture&&!speakerView),$('lecturePanel').hidden);
  $('shotNumber').textContent=opening?'总览':`0${shot+1} / ${SHOTS[shot].name}`;
  $('shotTitle').innerHTML=SHOTS[shot].title;
  $('shotDescription').textContent=SHOTS[shot].description;
  document.querySelectorAll('[data-shot]').forEach(b=>b.setAttribute('aria-current',String(Number(b.dataset.shot)===shot)));
  controlLabel($('tour'),touring?'暂停巡游':free?'恢复巡游':'继续巡游');
  $('tour').setAttribute('aria-pressed',String(touring));
  $('mode').textContent=opening?'总览 · 5 秒后进入板书':SHOTS[shot].lecture?'跟随当前板书':touring?'自动镜头':free?'自由观察':'镜头已暂停';
  $('world').dataset.mode=touring?'tour':free?'free':'paused';
  if(speakerView){$('shotNumber').textContent='报告厅 / 讲台';$('shotTitle').textContent='报告人视角';$('shotDescription').textContent='站在讲台后面向听众 · 触控屏可暂停或翻页 · 可自由转动观察';$('mode').textContent='报告人视角 · 手动观察';}
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
  shotPose();
  const rotation=camera.quaternion.clone(),endRotation=new THREE.Quaternion().setFromRotationMatrix(lookMatrix.lookAt(shotPosition,shotTarget,viewUp));
  blend={elapsed:0,position,target,fov:camera.fov,endPosition:shotPosition.clone(),endRotation,rotation,
    distance:position.distanceTo(target),endDistance:shotPosition.distanceTo(shotTarget),
    velocity:motionVelocity.clone(),acceleration:motionAcceleration.clone().clampLength(0,3),
    duration:reduced.matches?1.6:Math.max(transitionSeconds(position.distanceTo(shotPosition)),rotation.angleTo(endRotation)/(Math.PI/14))};
  frameSamples.length=0;cpuSamples.length=0;metricsAt=0;
  $('transition').style.opacity=0;
}
function selectShot(index,reportView=false){
  speakerView=false;
  choosingReport=reportView;opening=null;shot=index;time=.85;boardFollow.reset();touring=false;free=false;
  beginTransition();updateLabels();
}
function resumeTour(){
  speakerView=false;
  opening=null;choosingReport=false;boardFollow.reset();touring=true;free=false;
  beginTransition();updateLabels();
}
function enterSpeakerView(){
  opening=null;choosingReport=false;speakerView=true;touring=false;free=true;keys.clear();
  reader?.close();beginTransition();updateLabels();
}
function applyShot(dt){
  const s=speakerView?{fov:62}:SHOTS[shot];shotPose();const position=shotPosition,target=shotTarget;
  if(s.lecture&&lecture){
    // A steady board-height teaching camera follows the active pair, not a room orbit.
    if(!blend&&dt>0){position.lerpVectors(camera.position,position,1-Math.exp(-dt*.75));target.lerpVectors(controls.target,target,1-Math.exp(-dt*.75));}
  }
  const priorFov=camera.fov;
  if(blend){
    blend.elapsed+=dt;const t=Math.min(1,blend.elapsed/blend.duration),k=smoothProgress(t);
    for(const axis of ['x','y','z'])camera.position[axis]=motionCoordinate(blend.position[axis],blend.endPosition[axis],blend.velocity[axis],blend.acceleration[axis],blend.duration,t);
    camera.quaternion.slerpQuaternions(blend.rotation,blend.endRotation,k);
    viewDirection.set(0,0,-1).applyQuaternion(camera.quaternion);
    controls.target.copy(camera.position).addScaledVector(viewDirection,THREE.MathUtils.lerp(blend.distance,blend.endDistance,k));
    camera.fov=THREE.MathUtils.lerp(blend.fov,s.fov,k);$('transition').style.opacity=0;
    if(k===1)blend=null;
  }else{
    camera.position.copy(position);controls.target.copy(target);camera.fov=s.fov;
    $('transition').style.opacity=0;
  }
  if(camera.fov!==priorFov)camera.updateProjectionMatrix();controls.update();
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
const frameSamples=[],cpuSamples=[];let metricsAt=0;
function tick(stamp){
  const cpuStart=performance.now(),frameMs=lastTime?stamp-lastTime:0;
  const dt=Math.min(.05,(stamp-lastTime)/1000||0);lastTime=stamp;
  if(document.hidden||!entered)return;
  if(lecture)lecture.update(dt,reduced.matches);
  retreat?.campus.automaticDoors.update(dt,reduced.matches);
  if(opening){
    if(opening.started===null)opening.started=stamp;
    if(stamp-opening.started>=OPENING_OVERVIEW_MS)selectShot(0);
  }
  if(touring){
    if(!blend){const state=advanceShot(shot,time,dt,Number($('speed').value));time=state.time;if(shot!==state.index){shot=state.index;beginTransition();updateLabels();}}
    applyShot(dt);
  }else if(blend){
    applyShot(dt);
  }else if(!speakerView&&SHOTS[shot].lecture&&lecture&&boardFollow.following){
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
  if(stamp-lastUIStamp>=100){
    lastUIStamp=stamp;
    if(lecture){updateLectureUI();reader?.update();}
    if(!speakerView&&SHOTS[shot].lecture&&lecture){
      $('mode').textContent=reportProgress||reportLoadError||(choosingReport?'选择报告人 / 主题':boardFollow.following?'跟随当前板书':`自由观察 · ${Math.ceil(boardFollow.remaining)} 秒后跟随`);
      $('world').dataset.boardFollow=boardFollow.following?'following':'manual';
      $('world').dataset.board=String(lecture.clock.active);
    }else delete $('world').dataset.boardFollow;
    retreat.campus.lectern.update({playing:lecture.playing,page:lecture.clock.page,total:lecture.pages.length});
    $('world').dataset.camera=camera.position.toArray().map(x=>x.toFixed(3)).join(',');
    $('world').dataset.transition=blend?'moving':'settled';$('world').dataset.opening=opening?'overview':'complete';
    const prior=SHOTS.slice(0,shot).reduce((a,s)=>a+s.duration,0);
    $('timelineFill').style.transform=`scaleX(${(prior+time)/totalDuration})`;
    $('world').dataset.shot=String(shot);
    updateSceneTime();
  }
  constrainAboveWater(camera,controls.target,seaLevel*BUILDING_SCALE);
  if(motionSample&&dt>0){motionVelocity.subVectors(camera.position,previousPosition).divideScalar(dt);motionAcceleration.subVectors(motionVelocity,previousVelocity).divideScalar(dt);}
  previousPosition.copy(camera.position);previousVelocity.copy(motionVelocity);motionSample=true;
  if(!reduced.matches){retreat.ocean.material.uniforms.time.value+=dt;retreat.landscape.update(dt);retreat.fleet.update(dt);}
  if(profile.direct)renderer.render(scene,camera);else composer.render();
  if(frameMs>0&&frameMs<250){frameSamples.push(frameMs);cpuSamples.push(performance.now()-cpuStart);if(frameSamples.length>120){frameSamples.shift();cpuSamples.shift();}}
  if(stamp-metricsAt>1000&&frameSamples.length>20){metricsAt=stamp;const frames=[...frameSamples].sort((a,b)=>a-b),cpu=[...cpuSamples].sort((a,b)=>a-b);$('world').dataset.performance=JSON.stringify({frameP50:frames[Math.floor(frames.length*.5)],frameP95:frames[Math.floor(frames.length*.95)],cpuP95:cpu[Math.floor(cpu.length*.95)],calls:renderer.info.render.calls,triangles:renderer.info.render.triangles,direct:profile.direct});if(blend)$('world').dataset.transitionPerformance=$('world').dataset.performance;}

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
  $('loadMessage').textContent='正在安装六块升降黑板与报告板书…';
  const lectureRoot=new THREE.Group();lectureRoot.name='East-facing compact auditorium blackboards';configureLectureRoot(lectureRoot);scene.add(lectureRoot);
  lecture=await createLecture(lectureRoot,renderer);retreat.roomFill.apply(lectureRoot);
  reader=createChalkReader(lecture);
  installPhysicalControls();
  populateReport();
  if(reduced.matches){lecture.playing=false;lecture.staticPage();}
  if(!profile.direct){composer=new EffectComposer(renderer);composer.addPass(new RenderPass(scene,camera));
  bloom=new UnrealBloomPass(new THREE.Vector2(innerWidth,innerHeight),0,.25,1.6);bloom.enabled=false;composer.addPass(bloom);composer.addPass(new OutputPass());}
  setQuality();updateSceneTime();updateLabels();applyShot(0);$('transition').style.opacity=0;
  // Shader compilation failures are reported, not hidden behind an endless loader.
  renderer.debug.onShaderError=()=>fail(new Error('The scene shader could not compile'));
  await renderer.compileAsync(scene,camera);
  // Upload textures before the user moves to a previously unseen part of the site.
  const textures=new Set();scene.traverse(object=>{for(const material of Array.isArray(object.material)?object.material:[object.material])if(material)for(const value of Object.values(material))if(value?.isTexture)textures.add(value);});
  for(const texture of textures)renderer.initTexture(texture);
  // Submit off-screen geometry once as well, while the opaque loader is up.
  const culled=[];scene.traverse(object=>{if(object.isMesh&&object.frustumCulled){culled.push(object);object.frustumCulled=false;}});
  if(profile.direct)renderer.render(scene,camera);else composer.render();
  culled.forEach(object=>object.frustumCulled=true);
  $('world').dataset.ready='true';$('world').dataset.entered='false';
  $('loadMessage').textContent='海上书院已准备就绪';$('enterButton').hidden=false;$('enterButton').focus({preventScroll:true});
  renderer.setAnimationLoop(tick);
  // Fetch only manifests and covers in the background, without delaying entry.
  lecture.preloadReports();
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

function populateReport(){
  $('lecturePage').replaceChildren();
  for(const [i,page] of lecture.pages.entries()){
    const option=document.createElement('option'),copy=lecture.copy(i);option.value=String(i);option.textContent=`${copy.source} · ${copy.title}`;$('lecturePage').append(option);
  }
  $('reportSelect').value=lecture.report.id;
  $('lectureHeading').textContent=lecture.report.speaker+' · '+lecture.report.topic;
  for(const id of ['lectureSource','readerSource']){$(id).href=lecture.report.url;$(id).textContent=lecture.report.sourceLabel+' ↗';}
  $('world').dataset.report=lecture.report.id;
}
let changingLanguage=false,changingReport=false,reportLoadError='',reportProgress='',reportRequest=0;
async function switchReport(id){
  if(!lecture||changingLanguage)return;
  const request=++reportRequest;changingReport=true;reportLoadError='';
  $('reportSelect').value=id;
  reportProgress='正在切换至 '+$('reportSelect').selectedOptions[0].textContent+'…';
  $('lectureStatus').textContent=reportProgress;$('mode').textContent=reportProgress;
  $('reportSelect').setAttribute('aria-busy','true');
  try{if(!await lecture.setReport(id)||request!==reportRequest)return;populateReport();if(reduced.matches){lecture.playing=false;lecture.staticPage();}reader?.close();selectShot(0);}
  catch(error){if(request!==reportRequest)return;reportLoadError=error.message;$('lectureStatus').textContent=error.message;$('reportSelect').value=lecture.report.id;$('mode').textContent=error.message;}
  finally{if(request===reportRequest){changingReport=false;reportProgress='';$('reportSelect').setAttribute('aria-busy','false');}}
}
$('reportButton').addEventListener('click',()=>{if(!lecture||!cameraIntent.canActivate())return;$('lecturePanel').hidden=true;$('lectureButton').setAttribute('aria-expanded','false');selectShot(0,true);reader?.close();});
$('reportSelect').addEventListener('change',event=>switchReport(event.target.value));
async function switchChalkLanguage(){
  if(!lecture||changingLanguage||changingReport)return;changingLanguage=true;
  try{await lecture.setLanguage(lecture.language==='zh'?'en':'zh');
    for(const [i,option] of [...$('lecturePage').options].entries()){const copy=lecture.copy(i);option.textContent=`${copy.source} · ${copy.title}`;}reader?.update();
  }catch(error){$('lectureStatus').textContent=error.message;}finally{changingLanguage=false;}
}
function installPhysicalControls(){
  const ray=new THREE.Raycaster(),pointer=new THREE.Vector2();
  const hit=e=>{
    const rect=$('world').getBoundingClientRect();pointer.set((e.clientX-rect.left)/rect.width*2-1,1-(e.clientY-rect.top)/rect.height*2);
    scene.updateMatrixWorld(true);camera.updateMatrixWorld(true);ray.setFromCamera(pointer,camera);
    const candidate=ray.intersectObjects([...lecture.hoverTargets,...retreat.campus.automaticDoors.targets,...retreat.campus.lectern.targets],false)[0];if(!candidate||candidate.distance>15)return null;
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
    if(action==='lectern:view')enterSpeakerView();
    else if(action==='lectern:play')$('lecturePlay').click();
    else if(action==='lectern:previous')$('lecturePrevious').click();
    else if(action==='lectern:next')$('lectureNext').click();
    else if(action==='language')switchChalkLanguage();
    else if(action.startsWith('report:'))switchReport(action.slice(7));
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
  const status=reportProgress||reportLoadError||lecture.status();if(status!==lectureStatus){$('lectureStatus').textContent=status;lectureStatus=status;}
  $('lecturePlay').disabled=lecture.clock.ended;$('lectureNext').disabled=lecture.clock.page===lecture.pages.length-1;$('lecturePrevious').disabled=lecture.clock.page===0;
  controlLabel($('lecturePlay'),lecture.clock.ended?'报告已结束':lecture.playing?'暂停板书':'继续板书');$('lecturePlay').setAttribute('aria-pressed',String(lecture.playing));
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
