import {preparePanelShell,bindPanelDismissals} from './panel-shell.js?v=smart-voice-9';
import {capturePhoto,downloadPhoto} from './photo.js?v=photo-151';
import {regionAnchor,distanceLabel} from './region-distance.js';
import {twilightCloudFactor} from './twilight-clouds.js?v=cloud-rate-142';
import {hallOrbit} from './hall-orbit.js';
import {startDeferredTextures} from './deferred-textures.js?v=startup-flow-145';
import {acceptsStartupQuality} from './startup-probe.js';
import {RenderChangeGate} from './render-change-gate.js';
import {renderRoomAction} from './room-actions.js?v=skill-arc-85';
import {StartupQuality} from './startup-quality.js?v=cloud-ready-113';
import {WALK_MENU,installCoastWalks,walkProgress} from './coast-walks.js?v=coast-walk-16';
import {createMovementHud} from './movement-hud.js?v=altitude-speed-109';
import {openingArrival} from './opening-arrival.js?v=opening-boards-73';
import {KeyboardMotion} from './keyboard-motion.js?v=altitude-speed-109';
import {geographicDirectionToCampus} from './elliptic-site.js?v=true-north-coast-1';
import {hallSunStart,sunViewRate} from './hall-sun-view.js';
import {finishCampusLayout,relocateShots,buildingOffset} from './campus-layout.js';
import {createScreenWebview} from './screen-webview.js?v126';
import {VIDEO_SITES} from './smart-glass-hub.js?v109';
import {OPENING_POSE,OpeningCameraLock,openingFrameFov} from './opening-camera.js?v=handoff-105';
import {SunriseIntro} from './sunrise-intro.js?v122';
import {bindRenderActivity} from './render-activity.js?v=loading-visible-144';
import {FrameQuality} from './frame-quality.js?v=reading-pixels-76';
import {OceanBudget} from './ocean-budget.js?v=adaptive-ocean-2';
import {createSurfAudio} from './surf-audio.js?v104';
const surfAudio=createSurfAudio();
import {TimePresentation} from './time-presentation.js?v91-shore';
import {hallFloorRoute,curveClearsHall,cameraProbeRadius,HallPassageMask} from './hall-camera-route.js?v=sw-corner-1';
const hallPassageMask=new HallPassageMask();
import {GRAPHICS_PRESETS,recommendedGraphics,initialGraphics,resolutionRatio,readingPixelRatio} from './graphics-settings.js?v=smart-default-81';
import {createPerformanceMonitor} from './performance-monitor.js?v=smart-voice-9';
import {mobilePolicy,withDeadline} from './mobile-runtime.js?v81-imac';
import {createResidenceNotes} from './residence-notes.js?v76-villa';
import {RenderBudget,createGpuTimer} from './render-budget.js?v84-display';
import {classroomVisible} from './classroom-visibility.js?v57-proof-flow';
import {teachingRoomAt} from './room-context.js?v=campus-layout-20260926';
import {configureSeminarRoot,seminarFloor} from './seminar-layout.js?v57-proof-flow';
import {KM_REPORT} from './seminar-catalog.js?v57-proof-flow';
import {BUILDINGS,OUTDOOR_AREAS,buildingForShot} from './building-catalog.js?v=true-north-coast-1';
import * as THREE from 'three';
import {createBackgroundMusic} from './background-music.js?v=arrival-live-71';
import {controlLabel} from './control-label.js?v=22-handwritten-cover';
import {OrbitControls} from '../3d/vendor/OrbitControls.js';
import {EffectComposer} from './vendor/postprocessing/EffectComposer.js';
import {RenderPass} from './vendor/postprocessing/RenderPass.js';
import {UnrealBloomPass} from './vendor/postprocessing/UnrealBloomPass.js';
import {OutputPass} from './vendor/postprocessing/OutputPass.js';
import {createRetreat,createArrivalEnvironment} from './scene.js?v=cloud-layout-149';
import {createLecture} from './lecture.js?v=opening-play-11';
import {reportVoicePresentation} from './report-voice.js?v=smart-voice-9';
import {configureLectureRoot,lectureViewOffset,BUILDING_SCALE,DECK_Y,HALL,SEAT_ROWS,SEAT_COLUMNS} from './site-layout.js?v44-hall-clearance';
import {seaLevel} from './landscape-shape.js?v44-hall-clearance';
import {createChalkReader} from './chalk-reader.js?v=inline-root-1';
import {displayProfile,boardFraming} from './display-profile.js?v84-display';
import {configureCameraInput} from './camera-input.js?v=mouse-soft-110';
import {bindCameraIntent} from './camera-intent.js?v=smart-voice-9';
import {SHOTS,smoothProgress,advanceShot,transitionSeconds} from './camera-paths.js?v=concert-53';
import {BoardFollow} from './board-follow.js?v=smart-voice-9';
import {RetreatTime} from './retreat-time.js?v91-shore';
import {shanghaiHour,solarEvents,solarState} from './solar-state.js?v91-shore';
import {createShanghaiWeather} from './shanghai-weather.js?v=reflection-ready-115';
import {constrainAboveWater} from './camera-bounds.js?v=22-handwritten-cover';
import {bindPhysicalButtons,physicalHitAction} from './physical-buttons.js?v=smart-voice-9';
import {motionCoordinate} from './camera-motion.js';
let boardWritingStyle='refined';try{if(localStorage.getItem('refuge-board-writing-style')==='marck')boardWritingStyle='marck';}catch{}
const sceneTime=new RetreatTime(()=>new Date(),shanghaiHour),boardFollow=new BoardFollow();let visualHour=sceneTime.hour,lastShadowHour=sceneTime.hour,weatherReading=null,weatherStatus="loading";

const timePresentation=new TimePresentation(sceneTime.hour);
const sunriseIntro=new SunriseIntro(sceneTime,timePresentation);
sunriseIntro.prepare(solarEvents(sceneTime.date).sunrise);
visualHour=lastShadowHour=sceneTime.hour;
let changingVoice=false,voiceLoadError='';
const $=id=>document.getElementById(id);
for(const id of ['lecturePanel','settings','timePanel','performancePanel','chalkReader','seminarPanel'])preparePanelShell($(id));
bindPanelDismissals(document,[
 {panel:$('lecturePanel'),triggers:[$('lectureButton')],close:()=>{$('lecturePanel').hidden=true;$('lectureButton').setAttribute('aria-expanded','false');}},
 {panel:$('settings'),triggers:[$('settingsButton')],close:()=>showSettings(false)},
 {panel:$('timePanel'),triggers:[$('timeButton')],close:()=>closeTime()},
 {panel:$('performancePanel'),triggers:[$('performanceButton')],close:()=>performanceMonitor.close()},
 {panel:$('chalkReader'),triggers:[$('readerOpen')],close:()=>reader?.close()},
 {panel:$('seminarPanel'),triggers:[$('chapters')],close:()=>setSeminarPanel(false)}
]);
try{if(localStorage.getItem('refuge-board-highlight')==='off')$('boardHighlight').value='off';}catch{}

const performanceMonitor=createPerformanceMonitor();
const movementHud=createMovementHud($('openingHint'),$('movementHud'));
$('boardWritingStyle').value=boardWritingStyle;if(boardWritingStyle==='marck')$('boardWritingStyleStatus').textContent='Marck Script（舒展）· 原来的非笔顺显现方式。';
const residenceNotes=createResidenceNotes();
relocateShots(SHOTS);
// Building navigation frames the exterior; the opening path keeps its own indoor endpoint.
{
 const hall=SHOTS.find(s=>s.name==='报告厅'),offset=buildingOffset('01B');
 const eye=[HALL.west*BUILDING_SCALE+offset.x-13,DECK_Y*BUILDING_SCALE+HALL.clearHeight+1.8,HALL.south*BUILDING_SCALE+offset.z+11];
 const target=[(HALL.west+HALL.east)*.5*BUILDING_SCALE+offset.x,DECK_Y*BUILDING_SCALE+3.8,offset.z];
 hall.positions=[eye,eye.slice()];hall.targets=[target,target.slice()];hall.fov=58;hall.hallOrbit=true;
}

installCoastWalks(SHOTS);
{const o=buildingOffset('01B'),p=[24*BUILDING_SCALE+o.x-40,.275*BUILDING_SCALE,o.z];SHOTS.push({name:'海上小亭',title:'沿廊入海，停在风里。',description:'曲线石板步道 · 四角攒尖海上亭',duration:30,fov:58,positions:[[p[0]+20,12,p[2]+22],[p[0]+20,12,p[2]+22]],targets:[[p[0]+5,1,p[2]],[p[0]+5,1,p[2]]]});BUILDINGS[0].rooms.push({name:'海上小亭',shot:'海上小亭'});}
for(const [label,event] of [['看日出','sunrise'],['看日落','sunset']]){const shift=buildingOffset('01B'),x=(event==='sunrise'?SEAT_ROWS[2].x-3.3:SEAT_ROWS[0].x+3.3)*BUILDING_SCALE+shift.x,p=[x,(DECK_Y+.028)*BUILDING_SCALE+(event==='sunrise'?SEAT_ROWS[2].rise:SEAT_ROWS[0].rise)+2.65,shift.z],t=[x+(event==='sunrise'?100:-100),p[1],p[2]];SHOTS.push({name:'报告厅'+label,title:label,description:event==='sunset'?'后排座椅前景 · 海平面日落':'第一排座椅前景 · 海平面日出',duration:30,fov:55,positions:[p,p.slice()],targets:[t,t.slice()]});BUILDINGS[0].rooms.push({name:label,sunEvent:event});}
BUILDINGS[0].rooms.push({name:'降下讲台',lecternLift:true});

OUTDOOR_AREAS.push('远眺','报告厅备份','访客小院','休息室二组');
for(const [i,n] of [[3,'共研工坊'],[4,'数学实验室'],[5,'北食阁'],[6,'南食阁'],[7,'休息室一组'],[8,'休息室三组']])BUILDINGS[i].name=n;
let panelBuilding=BUILDINGS[0];
for(const item of [...BUILDINGS,...OUTDOOR_AREAS.filter(name=>!['曲线海岸总览','左环漫滩','主楼沙滩'].includes(name)).map(name=>({name,shot:name}))]){
  const button=document.createElement('button');button.dataset.shot=String(SHOTS.findIndex(s=>s.name===item.shot));
  button.textContent=(item.number?['1','07','02','03','04','05N','05S','R1','R3','10'][item.number-1]+'  ':'')+item.name;
  if(item.number){button.dataset.building=String(item.number);button.setAttribute('aria-controls','seminarPanel');button.setAttribute('aria-expanded','false');}
  if(item.number===2)button.id='seminarButton';$('chapters').append(button);
}
const walkButton=document.createElement('button');walkButton.id='walkButton';walkButton.textContent='漫步';walkButton.setAttribute('aria-controls','seminarPanel');walkButton.setAttribute('aria-expanded','false');$('chapters').append(walkButton);
walkButton.addEventListener('click',()=>{if(retreat&&cameraIntent.canActivate())setSeminarPanel($('seminarPanel').hidden||!panelBuilding.walk,WALK_MENU);});
const openingButton=document.createElement('button');openingButton.id='replayOpening';openingButton.textContent='开场';openingButton.setAttribute('aria-label','重新播放开场');$('chapters').prepend(openingButton);
const backgroundMusic=createBackgroundMusic({audio:$('backgroundMusic'),button:$('musicButton'),volume:$('musicVolume'),readout:$('musicVolumeValue')});
const screenWebview=createScreenWebview(THREE);
let entered=false,openingPreparing=false,openingPrepared=false;
const openingCameraLock=new OpeningCameraLock();
const cameraLocked=()=>openingPreparing||openingCameraLock.locked(performance.now());
// Capture before OrbitControls and scene hit targets, while other settings remain usable.
for(const type of ['pointerdown','wheel','click','dblclick'])document.addEventListener(type,event=>{
 if(cameraLocked()&&event.target.closest?.('#world,#chapters,#tour,#roomControls,#buildingRooms,#lecternConsole,#lecturePanel')){event.preventDefault();event.stopImmediatePropagation();}
},{capture:true,passive:false});
let entryTransition=false;
async function enterScene(){
  if(entered||entryTransition||$('world').dataset.ready!=='true'||!window.refugeBoot?.authorized||!window.refugeBoot?.previewReady)return;
  entryTransition=true;await window.refugeBoot?.exitCoast?.();
  entered=true;entryTransition=false;window.refugeBoot?.entered();lastTime=performance.now();$('loading').hidden=true;$('world').dataset.entered='true';
  backgroundMusic.start();surfAudio.setEnabled(true).catch(console.error);$('surfSound').value='on';
  replayOpening(true).catch(fail);
  $('world').focus({preventScroll:true});
  renderActivity.setEnabled(!failed);
}
async function replayOpening(preserveInitialView=false){
  if(!entered||!retreat||cameraLocked())return;
  screenWebview.close();if(activeRoom!==0)activateRoom(0,false);
  openingPreparing=true;
  try{
    motionVelocity.set(0,0,0);motionAcceleration.set(0,0,0);motionSample=false;
    controls.enableDamping=false;controls.update();
    if(!preserveInitialView){camera.position.fromArray(OPENING_POSE.position);controls.target.fromArray(OPENING_POSE.target);camera.fov=openingFrameFov(camera.aspect);camera.updateProjectionMatrix();}
    controls.update();controls.enableDamping=true;
    blend=null;opening=null;free=true;touring=false;controls.enabled=false;
    if(!openingPrepared)await lecture.prepareOpening();openingPrepared=false;populateReport();
    retreat.fleet.resetSunrisePass();
    if(!sunriseIntro.waiting)sunriseIntro.prepare(solarEvents(sceneTime.date).sunrise);
    visualHour=lastShadowHour=sceneTime.hour;$('timeRate').value='1';
    openingCameraLock.start(performance.now());keys.clear();controls.enabled=false;
    selectShot(SHOTS.findIndex(s=>s.name==='报告厅'),false,true);
    const offset=buildingOffset('01B'),end=[SEAT_ROWS[1].x*BUILDING_SCALE+offset.x-.65,(DECK_Y+.028)*BUILDING_SCALE+SEAT_ROWS[1].rise+1.65,offset.z];
    blend.openingPath=openingArrival(camera.position.toArray(),HALL.west*BUILDING_SCALE+offset.x,offset.z,end,{x:retreat.campus.seaPavilion.position.x,bridgeX:retreat.campus.seaPavilion.root.position.x});blend.duration=blend.openingPath.duration;blend.route=null;blend.endPosition.fromArray(end);blend.endRotation.setFromRotationMatrix(lookMatrix.lookAt(new THREE.Vector3(...end),new THREE.Vector3(end[0]+20,end[1],end[2]),viewUp));
    $('world').focus({preventScroll:true});
    renderActivity.setEnabled(!failed);
  }finally{openingPreparing=false;}
}
openingButton.addEventListener('click',()=>replayOpening().catch(fail));
window.addEventListener('refuge-entry',enterScene);
const device=mobilePolicy({width:innerWidth,height:innerHeight,userAgent:navigator.userAgent,maxTouchPoints:navigator.maxTouchPoints,coarsePointer:matchMedia('(pointer: coarse)').matches,safe:new URLSearchParams(location.search).get('safe')==='1'});
$('world').dataset.deviceProfile=device.mobile?'mobile':'desktop';
const reduced=matchMedia('(prefers-reduced-motion: reduce)');
let renderer,composer,camera,controls,cameraInput,cameraIntent,retreat,bloom,lecture,reader,profile,nativeSamples=0,failed=false;
let shot=SHOTS.findIndex(s=>s.name==='远眺'),time=SHOTS[shot].duration*.62,lastTime=0,touring=false,free=false,blend=null,opening={started:null};
const keys=new Set(),keyboardMotion=new KeyboardMotion(),scene=new THREE.Scene();
const curves=SHOTS.map(s=>({
  position:new THREE.CatmullRomCurve3(s.positions.map(p=>new THREE.Vector3(...p))),
  target:new THREE.CatmullRomCurve3(s.targets.map(p=>new THREE.Vector3(...p)))
}));
const totalDuration=SHOTS.reduce((a,s)=>a+s.duration,0);
const motionVelocity=new THREE.Vector3(),motionAcceleration=new THREE.Vector3(),previousPosition=new THREE.Vector3(),previousVelocity=new THREE.Vector3();
const shotPosition=new THREE.Vector3(),shotTarget=new THREE.Vector3(),viewDirection=new THREE.Vector3(),lookMatrix=new THREE.Matrix4(),viewUp=new THREE.Vector3(0,1,0);
const rooms=[],roomLecterns=[],roomViews=[],campusLightTarget=new THREE.Vector3(12*BUILDING_SCALE,3*BUILDING_SCALE,0);
const roomFrustum=new THREE.Frustum(),roomProjection=new THREE.Matrix4();let visibilityAt=-Infinity;
function updateRoomVisibility(stamp){
  if(stamp-visibilityAt<100)return;visibilityAt=stamp;camera.updateMatrixWorld();retreat?.updateGeometryLOD(camera,innerHeight,$('geometryDetail').value==='full');
  roomFrustum.setFromProjectionMatrix(roomProjection.multiplyMatrices(camera.projectionMatrix,camera.matrixWorldInverse));
  const insideRoom=teachingRoomAt(camera.position);
  roomViews.forEach((v,i)=>{
    const visible=classroomVisible({distance:v.bounds.distanceToPoint(camera.position),inFrustum:roomFrustum.intersectsBox(v.bounds),eyeY:camera.position.y,floorY:v.floor,height:v.height,insideRoom,room:i,wasVisible:v.visible});
    if(visible!==v.visible){v.visible=visible;rooms[i].setRenderActive(visible);}
    v.consoleVisible=classroomVisible({distance:v.consoleBounds.distanceToPoint(camera.position),inFrustum:roomFrustum.intersectsBox(v.consoleBounds),eyeY:camera.position.y,floorY:v.floor,height:v.height,insideRoom,room:i,wasVisible:v.consoleVisible});
    roomLecterns[i].group.visible=true;
    roomLecterns[i].setScreenEnabled(v.consoleVisible&&!rooms[i].disabled&&rooms[i].screenMode?.power!==false);
  });
  $('world').dataset.renderingRooms=rooms.map((room,i)=>room.renderActive?i:null).filter(i=>i!==null).join(',');
}
let activeRoom=0,physicalRoom=-1;
let motionSample=false,lastUIStamp=0,choosingReport=false,speakerView=false;
function shotPose(){
  if(speakerView){const pose=roomLecterns[activeRoom].speakerPose(camera.aspect);shotPosition.copy(pose.position);shotTarget.copy(pose.target);return;}
  const s=SHOTS[shot],t=s.walk?walkProgress(time,s.duration):smoothProgress(time/s.duration);
  curves[shot].position.getPointAt(t,shotPosition);curves[shot].target.getPointAt(t,shotTarget);
  if(s.hallOrbit&&!touring){shotPosition.fromArray(hallOrbit(s.positions[0],s.targets[0],time));shotTarget.fromArray(s.targets[0]);}
  if(s.lecture&&lecture){
    const framing=boardFraming(camera.aspect,s.fov);shotTarget.copy(choosingReport?lecture.reportFocus():lecture.focus(true));
    shotPosition.copy(shotTarget).add(viewDirection.fromArray([-(choosingReport?Math.max(4.6,framing.distance):framing.distance)*lecture.viewScale,0,0]));
  }
}
function fail(error){
  failed=true;renderActivity.setEnabled(false);window.refugeBoot?.fail(error);
}
function updateRegionDistance(){
 const current=SHOTS[shot],building=current.lecture?BUILDINGS[activeRoom===0?0:1]:buildingForShot(current.name);
 const destination=building?SHOTS.find(s=>s.name===building.shot):current;
 const value=opening?'':distanceLabel(camera.position.toArray(),regionAnchor(destination));
 const output=$('shotDistance');output.hidden=!value;if(output.textContent!==value)output.textContent=value;
 output.title='镜头至'+(building?.name||current.name)+'定位点的空间直线距离';
}
function updateLabels(){
  updateRegionDistance();
  residenceNotes.update(SHOTS[shot].name);
  document.body.classList.toggle('teaching',Boolean(SHOTS[shot].lecture&&!speakerView));
  reader?.chapter(Boolean(SHOTS[shot].lecture&&!speakerView)&&teachingRoomAt(camera.position)===activeRoom,$('lecturePanel').hidden);
  $('shotNumber').textContent=opening?'总览':`${String(shot+1).padStart(2,'0')} / ${SHOTS[shot].name}`;
  $('shotTitle').innerHTML=SHOTS[shot].title;
  $('shotDescription').textContent=SHOTS[shot].description;
  const building=SHOTS[shot].lecture?BUILDINGS[activeRoom===0?0:1]:buildingForShot(SHOTS[shot].name);
  const area=building?SHOTS.findIndex(s=>s.name===building.shot):shot;
  if(!opening)$('shotNumber').textContent=SHOTS[shot].lecture?(activeRoom===0?'报告厅':'教学楼 '+activeRoom+' 层')+' / 板书':(building?building.number+' / ':'')+(building?.name||SHOTS[shot].name);
  document.querySelectorAll('#chapters button[data-shot]').forEach(b=>b.setAttribute('aria-current',String(Number(b.dataset.shot)===area)));
  controlLabel($('tour'),touring?'暂停巡游':free?'恢复巡游':'继续巡游');
  $('tour').setAttribute('aria-pressed',String(touring));
  $('mode').textContent=opening?'左环漫滩上空 · 即将进入报告厅':SHOTS[shot].lecture?'跟随当前板书':touring?'自动镜头':free?'自由观察':SHOTS[shot].hallOrbit&&!reduced.matches?'报告厅 · 缓慢环绕':'镜头已暂停';
  $('world').dataset.mode=touring?'tour':free?'free':'paused';
  if(SHOTS[shot].walk){walkButton.setAttribute('aria-current','true');$('mode').textContent=free?'自由观察':'沿岸漫步 · 操作镜头即可接管';}else walkButton.removeAttribute('aria-current');
  if(speakerView){$('shotNumber').textContent=(activeRoom===0?'报告厅':'教学楼 '+activeRoom+' 层')+' / 讲台';$('shotTitle').textContent='报告人视角';$('shotDescription').textContent='站在讲台后面向听众 · 触控屏可暂停或翻页 · 可自由转动观察';$('mode').textContent='报告人视角 · 手动观察';}
}
function stopTour(){
  if(cameraLocked())return;
  if(sunriseIntro.waiting){sunriseIntro.cancel();sceneTime.setRate(1);sceneTime.sync();$('timeRate').value='1';}
  opening=null;
  if(SHOTS[shot].lecture)boardFollow.touch();
  const changed=touring||!free||blend;
  touring=false;free=true;blend=null;$('transition').style.opacity=0;
  if(changed)updateLabels();
}
function beginTransition(){
  keys.clear();keyboardMotion.reset();
  const position=camera.position.clone(),target=controls.target.clone(),damping=controls.enableDamping;
  controls.enableDamping=false;controls.update();camera.position.copy(position);controls.target.copy(target);controls.update();controls.enableDamping=damping;
  shotPose();
  const rotation=camera.quaternion.clone(),endRotation=new THREE.Quaternion().setFromRotationMatrix(lookMatrix.lookAt(shotPosition,shotTarget,viewUp));
  blend={elapsed:0,position,target,fov:camera.fov,endPosition:shotPosition.clone(),endRotation,rotation,
    distance:position.distanceTo(target),endDistance:shotPosition.distanceTo(shotTarget),
    velocity:motionVelocity.clone(),acceleration:motionAcceleration.clone().clampLength(0,3),
    duration:reduced.matches?1.6:Math.max(transitionSeconds(position.distanceTo(shotPosition)),rotation.angleTo(endRotation)/(Math.PI/14))};
  const route=hallFloorRoute(position.toArray(),shotPosition.toArray());if(route){const points=route.map(p=>new THREE.Vector3(...p));blend.route=new THREE.CatmullRomCurve3(points,false,'centripetal');if(!curveClearsHall(blend.route,cameraProbeRadius(camera.near,Math.max(camera.fov,SHOTS[shot].fov||60),camera.aspect))){const safe=new THREE.CurvePath();for(let i=1;i<points.length;i++)safe.add(new THREE.LineCurve3(points[i-1],points[i]));blend.route=safe;}blend.duration=Math.max(blend.duration,blend.route.getLength()/3.2);}
  frameSamples.length=0;cpuSamples.length=0;metricsAt=0;
  $('transition').style.opacity=0;
}
function selectShot(index,reportView=false,openingArrival=false){
  if(cameraLocked()&&!openingArrival)return;
  if(sunriseIntro.waiting&&!openingArrival){sunriseIntro.cancel();sceneTime.setRate(1);sceneTime.sync();$('timeRate').value='1';}
  speakerView=false;
  choosingReport=reportView;opening=null;shot=index;time=SHOTS[index].walk||SHOTS[index].hallOrbit?0:.85;boardFollow.reset();touring=false;
  // Opening borrows the hall label, not its exterior orbit. Keep its final sunrise pose.
  free=openingArrival;
  beginTransition();blend.openingArrival=openingArrival;updateLabels();
  if(SHOTS[index].walk)setSeminarPanel(true,WALK_MENU);
  else if(!SHOTS[index].lecture){const building=buildingForShot(SHOTS[index].name);setSeminarPanel(Boolean(building),building);}
}
function resumeTour(){
  if(cameraLocked())return;
  speakerView=false;
  opening=null;choosingReport=false;boardFollow.reset();touring=true;free=false;
  beginTransition();updateLabels();
}
function enterSpeakerView(){
  if(cameraLocked())return;
  opening=null;choosingReport=false;speakerView=true;touring=false;free=true;keys.clear();
  reader?.close();beginTransition();updateLabels();
}
function applyShot(dt){
  const s=speakerView?roomLecterns[activeRoom].speakerPose(camera.aspect):SHOTS[shot];shotPose();const position=shotPosition,target=shotTarget;
  if(s.lecture&&lecture){
    // A steady board-height teaching camera follows the active pair, not a room orbit.
    if(!blend&&dt>0){position.lerpVectors(camera.position,position,1-Math.exp(-dt*.75));target.lerpVectors(controls.target,target,1-Math.exp(-dt*.75));}
  }
  const priorFov=camera.fov;
  if(blend){
    blend.elapsed+=dt;const t=Math.min(1,blend.elapsed/blend.duration),k=smoothProgress(t);
    for(const axis of ['x','y','z'])camera.position[axis]=motionCoordinate(blend.position[axis],blend.endPosition[axis],blend.velocity[axis],blend.acceleration[axis],blend.duration,t);
    if(blend.openingPath){
      camera.position.fromArray(blend.openingPath.sample(blend.elapsed));
      if(!blend.openingBoardStarted&&camera.position.x>=blend.openingPath.hallEntranceX){
        blend.openingBoardStarted=true;if(!rooms[0].openingNarrated)rooms[0].beginOpening(reduced.matches);
      }
    }
    else if(blend.route)blend.route.getPointAt(k,camera.position);
    camera.quaternion.slerpQuaternions(blend.rotation,blend.endRotation,k);
    viewDirection.set(0,0,-1).applyQuaternion(camera.quaternion);
    controls.target.copy(camera.position).addScaledVector(viewDirection,THREE.MathUtils.lerp(blend.distance,blend.endDistance,k));
    camera.fov=THREE.MathUtils.lerp(blend.fov,s.fov,k);$('transition').style.opacity=0;
    if(k===1){
      const arrival=blend.openingArrival;blend=null;
      if(arrival){
        sunriseIntro.arrive();retreat.fleet.startSunrisePass();
        if(rooms[0].openingNarrated){
          const openingLecture=rooms[0];
          void Promise.resolve(openingLecture.beginOpening(reduced.matches)).then(started=>{
            if(started&&lecture===openingLecture){populateReport();reader?.close();selectShot(0);}
          }).catch(fail);
        }else{
          const forward=controls.target.clone().sub(camera.position);forward.y=0;forward.normalize();
          // A small, interruptible indoor push with zero speed at both ends.
          blend={elapsed:0,duration:15,position:camera.position.clone(),endPosition:camera.position.clone().addScaledVector(forward,.65),
            target:controls.target.clone(),rotation:camera.quaternion.clone(),endRotation:camera.quaternion.clone(),
            fov:camera.fov,distance:camera.position.distanceTo(controls.target),endDistance:camera.position.distanceTo(controls.target),
            velocity:new THREE.Vector3(),acceleration:new THREE.Vector3(),settling:true};
        }
      }
    }
  }else{
    camera.position.copy(position);controls.target.copy(target);camera.fov=s.fov;
    $('transition').style.opacity=0;
  }
  if(camera.fov!==priorFov)camera.updateProjectionMatrix();controls.update();
}
function resize(){
  if(!renderer)return;
  profile=displayProfile(innerWidth,innerHeight,devicePixelRatio,$('quality').value,renderer.capabilities.maxSamples,nativeSamples,device);
  profile.pixelRatio=resolutionRatio(profile.pixelRatio,$('resolutionScale').value,innerWidth,innerHeight,renderer.capabilities.maxTextureSize);profile.shadows=Number($('shadowQuality').value)>0;profile.shadowSize=Number($('shadowQuality').value)||1024;
  camera.aspect=innerWidth/innerHeight;if(!entered)camera.fov=openingFrameFov(camera.aspect);camera.updateProjectionMatrix();
  if(speakerView&&retreat){camera.fov=roomLecterns[activeRoom].speakerPose(camera.aspect).fov;camera.updateProjectionMatrix();}
  renderBudget.reset();renderScale=1;
  const bufferRatio=readingPixelRatio(profile.pixelRatio,{enabled:$('boardClarity').value==='crisp',mobile:device.mobile,width:innerWidth,height:innerHeight,dpr:devicePixelRatio,maxTextureSize:renderer.capabilities.maxTextureSize});
  // Reserve readable board resolution before entry; never allocate it at the hall door.
  // One backing-store resize, rather than reallocating once for DPR and again for size.
  if(renderer.domElement.width!==Math.floor(innerWidth*bufferRatio)||renderer.domElement.height!==Math.floor(innerHeight*bufferRatio)||renderer.getPixelRatio()!==bufferRatio)renderer.setDrawingBufferSize(innerWidth,innerHeight,bufferRatio);
  if(composer){
    // Dispose on sample-count changes: changing .samples alone does not rebuild
    // an already allocated WebGL framebuffer at the same dimensions.
    for(const target of [composer.renderTarget1,composer.renderTarget2])if(target.samples!==profile.samples){target.samples=profile.samples;target.dispose();}
    composer.setPixelRatio(profile.direct?1:bufferRatio);composer.setSize(innerWidth,innerHeight);
    bloom.enabled=false; // Chalk and stone must never acquire a screen-space halo.
  }
  renderer.shadowMap.enabled=profile.shadows;renderer.shadowMap.needsUpdate=true;
  if(retreat&&retreat.sun.shadow.mapSize.x!==profile.shadowSize){retreat.sun.shadow.mapSize.set(profile.shadowSize,profile.shadowSize);retreat.sun.shadow.map?.dispose();retreat.sun.shadow.map=null;}
  updateQualityReadout();
}
function updateQualityReadout(){
  const ratio=renderer.getPixelRatio();
  $('resolutionValue').textContent=$('resolutionScale').value+'%';
  $('qualityReadout').textContent=`${ratio.toFixed(2)}× 分辨率 · ${profile.direct?nativeSamples:profile.samples}× 抗锯齿${renderScale<1?' · 自动平衡':''}`;
  $('world').dataset.pixelRatio=String(ratio);$('world').dataset.renderScale=String(renderScale);$('world').dataset.antialias=String(profile.direct?nativeSamples:profile.samples);
}
function updateRenderBudget(stamp){
  const ms=gpuTimer?.poll(stamp);if(ms!=null){renderBudget.sample(ms,stamp);performanceMonitor.gpu(ms,stamp);}
  const reading=rooms.some((room,i)=>roomViews[i]?.visible&&room.hasSelection&&(!room.stored||room.storageProgress<1)&&!room.disabled);
  const protectReading=$('boardClarity').value==='crisp';
  const pixelRatio=readingPixelRatio(profile.pixelRatio,{enabled:protectReading&&$('adaptiveQuality').value==='auto',mobile:device.mobile,width:innerWidth,height:innerHeight,dpr:devicePixelRatio,maxTextureSize:renderer.capabilities.maxTextureSize});
  const settings=frameQuality.settings({reading:protectReading||reading,clarity:$('boardClarity').value,pixelRatio,cloud:$('cloudQuality').value,shadow:Number($('shadowQuality').value)});
  if(activeCloudQuality!==settings.cloud&&(renderChangeGate.ready||['off','low','medium','high'].indexOf(settings.cloud)<['off','low','medium','high'].indexOf(activeCloudQuality))){activeCloudQuality=settings.cloud;retreat.sky.userData.setCloudQuality(activeCloudQuality);}
  const shadows=settings.shadow>0;
  if(renderer.shadowMap.enabled!==shadows&&(!shadows||renderChangeGate.ready)){renderer.shadowMap.enabled=shadows;renderer.shadowMap.needsUpdate=true;}
  if(shadows&&retreat.sun.shadow.mapSize.x!==settings.shadow&&(renderChangeGate.ready||settings.shadow<retreat.sun.shadow.mapSize.x)){retreat.sun.shadow.mapSize.set(settings.shadow,settings.shadow);retreat.sun.shadow.map?.dispose();retreat.sun.shadow.map=null;renderer.shadowMap.needsUpdate=true;}
  const water=retreat.ocean.material.uniforms;
  water.waterDetail.value=!settings.simpleWater&&$('waterDetail').value==='high'?1:0;
  water.reflectionDetail.value=!settings.simpleWater&&$('waterReflection').value==='full'?1:0;
  retreat.sky.material.uniforms.starsEnabled.value=$('starEffects').value==='on'?1:0;
  retreat.sky.material.uniforms.meteorEnabled.value=settings.particles&&$('meteorEffects').value==='on'?1:0;
  const targetFPS=frameQuality.stats?.target||Math.min(Number($('targetFPS').value),60);
  const gpuScale=renderBudget.update(stamp,{enabled:$('adaptiveQuality').value==='auto',reading:protectReading||reading,mobile:device.mobile,targetFPS,protectText:true});
  const scale=Math.min(gpuScale,settings.scale);
  if((renderChangeGate.ready||scale<renderScale||protectReading&&renderer.getPixelRatio()<pixelRatio)&&(scale!==renderScale||Math.abs(renderer.getPixelRatio()-pixelRatio*scale)>.0001)){
    renderScale=scale;renderer.setDrawingBufferSize(innerWidth,innerHeight,pixelRatio*scale);
    if(composer&&!profile.direct)composer.setPixelRatio(pixelRatio*scale);
    updateQualityReadout();
  }
  const text=$('adaptiveQuality').value!=='auto'?'固定画质':(frameQuality.level===0?'自动 · 按实际帧率监测':`自动降级 ${frameQuality.level}/5 · 云${settings.cloud==='off'?'关闭':settings.cloud==='low'?'标准':'精细'} · 阴影${shadows?'标准':'关闭'} · 渲染 ${Math.round(scale*100)}%`)+(protectReading?' · 板书清晰保护':'');
  if($('adaptiveReadout').textContent!==text)$('adaptiveReadout').textContent=text;
  if($('world').dataset.adaptiveLevel!==String(frameQuality.level))$('world').dataset.adaptiveLevel=String(frameQuality.level);

}
const graphicsKeys=['oceanModel','quality','resolutionScale','shadowQuality','cloudQuality','textureFiltering','waterDetail','targetFPS','adaptiveQuality','rainEffects','starEffects','geometryDetail','windWaves','waveStrength','waterReflection','sunReflection','nightStyle','meteorEffects','sunSize'];
let gpuName='',activeCloudQuality='off',desiredGraphics=null;const startupQuality=new StartupQuality(),renderChangeGate=new RenderChangeGate();let startupAutomatic=true;
function saveGraphics(){try{localStorage.setItem('refuge-graphics-v84',JSON.stringify(Object.fromEntries(graphicsKeys.map(k=>[k,$(k).value]))));}catch{}}
function setQuality(){
  frameQuality.reset();resize();if(!retreat)return;
  oceanBudget.configure($('oceanModel').value,Number($('targetFPS').value));
  applyOceanQuality();
  activeCloudQuality=$('cloudQuality').value;retreat.sky.userData.setCloudQuality(activeCloudQuality);
  retreat.sky.userData.solarSize=$('sunSize').value;
  retreat.sky.material.uniforms.nightStyle.value=$('nightStyle').value==='vivid'?1:0;retreat.sky.material.uniforms.meteorEnabled.value=$('meteorEffects').value==='on'?1:0;
  retreat.sky.material.uniforms.starsEnabled.value=$('starEffects').value==='on'?1:0;
  retreat.ocean.material.uniforms.waterDetail.value=$('waterDetail').value==='high'?1:0;
  retreat.ocean.material.uniforms.windWaves.value=$('windWaves').value==='on'?1:0;retreat.ocean.material.uniforms.waveStrength.value=Math.max(.5,Number($('waveStrength').value)/100);retreat.ocean.material.uniforms.reflectionDetail.value=$('waterReflection').value==='full'?1:0;retreat.ocean.material.uniforms.sunReflection.value=$('sunReflection').value==='on'?1:0;$('waveStrengthValue').textContent=$('waveStrength').value+'%';
  const anisotropy=Math.min(Number($('textureFiltering').value),renderer.capabilities.getMaxAnisotropy()),seen=new Set();
  scene.traverse(o=>{if(o.userData.boardSurface)return;for(const m of Array.isArray(o.material)?o.material:[o.material])if(m)for(const key of ['map','normalMap','roughnessMap']){const t=m[key];if(t&&!seen.has(t)&&!t.isRenderTargetTexture){seen.add(t);if(t.anisotropy!==anisotropy){t.anisotropy=anisotropy;t.needsUpdate=true;}}}});
  rooms.forEach(room=>{room.setClarity($('boardClarity').value);room.setHighlight($('boardHighlight').value!=='off');});
}
function markManualGraphics(){ $('world').dataset.graphicsMode='manual';$('recommendStatus').textContent='当前使用手动配置 · 下次进入仍自动检测并采用智能推荐。'; }
function applyGraphics(values){markManualGraphics();startupAutomatic=false;device.startup=false;for(const [id,value] of Object.entries(values)){const el=$(id);if(el&&graphicsKeys.includes(id))el.value=value;}setQuality();saveGraphics();}
function detectGraphics(){
 const gl=renderer.getContext(),ext=gl.getExtension('WEBGL_debug_renderer_info');gpuName=ext?gl.getParameter(ext.UNMASKED_RENDERER_WEBGL):'图形型号未公开';
 $('deviceReadout').textContent=gpuName.replace(/^ANGLE \(/,'').replace(/^NVIDIA, /,'').split(' (0x')[0].slice(0,100)+' · '+innerWidth+' × '+innerHeight;
 let saved;try{saved=JSON.parse(localStorage.getItem('refuge-graphics-v84'));}catch{}
 desiredGraphics=initialGraphics({mobile:device.mobile,gpu:gpuName,maxTextureSize:renderer.capabilities.maxTextureSize},Object.fromEntries(graphicsKeys.map(k=>[k,$(k).value])),saved);
 $('world').dataset.graphicsMode='smart';
 $('recommendStatus').textContent='智能推荐已应用 · 优先准备天气与高清板书。';
 startupQuality.level=device.safe?0:2;device.startup=device.safe;
 const values=startupQuality.settings(desiredGraphics);
 for(const [id,value] of Object.entries(values)){if(graphicsKeys.includes(id)&&$(id).querySelector?.('option[value="'+value+'"]'))$(id).value=value;else if((id==='resolutionScale'&&Number(value)>=75&&Number(value)<=150)||(id==='waveStrength'&&Number(value)>=50&&Number(value)<=150))$(id).value=value;}
}
const frameQuality=new FrameQuality();
const oceanBudget=new OceanBudget();
const oceanNames=['01 曲线海岸 · 简化细节','01 曲线海岸 · 标准','01 曲线海岸 · 完整'];
function applyOceanQuality(){
 const mode=$('oceanModel').value;
 // Room boundaries do not change shader variants; the measured budget owns the tier.
 const level=mode==='auto'&&frameQuality.level>0?0:oceanBudget.level;
 const water=retreat.ocean.material.uniforms;water.oceanLite.value=level===0?1:0;
 retreat.ocean.userData.study.setQuality(level);
 const text=(mode==='auto'?'自动 · ':'手动 · ')+oceanNames[level];
 if($('oceanQualityReadout').textContent!==text)$('oceanQualityReadout').textContent=text;
 $('world').dataset.oceanQuality=['lite','classic','study'][level];
 if(oceanBudget.stats)$('world').dataset.oceanPerformance=JSON.stringify(oceanBudget.stats);
}
const renderBudget=new RenderBudget();let gpuTimer=null,weatherTimer=null,renderScale=1,weatherGpuMs=null,weatherGpuSamples=[],weatherCpuMs=0,weatherProbeFrame=false,weatherProbeCounter=0;
const frameSamples=[],cpuSamples=[];let metricsAt=0;
const renderActivity=bindRenderActivity({allowUnfocused:()=>!entered,setLoop:callback=>renderer?.setAnimationLoop(callback),frame:tick,
 onPause(){
  keys.clear();gpuTimer?.dispose();weatherTimer?.dispose();
  $('world').dataset.renderActivity='paused';performanceMonitor.setPaused(true);
 },
 onResume(gap){
  lastTime=0;motionSample=false;visibilityAt=-Infinity;lastUIStamp=-Infinity;
  if(opening?.started!=null)opening.started+=gap;
  if(Number.isFinite(boardFollow.lastInput))boardFollow.lastInput+=gap/1000;
  frameSamples.length=0;cpuSamples.length=0;weatherGpuSamples.length=0;weatherGpuMs=null;
  oceanBudget.resetSamples();frameQuality.resetSamples();startupQuality.resetSamples();
  renderBudget.samples.length=0;renderBudget.gpuMs=null;renderBudget.lastSampleAt=0;
  $('world').dataset.renderActivity='running';performanceMonitor.setPaused(false);
 }
});
$('world').dataset.renderActivity='waiting';
device.isRenderActive=()=>renderActivity.foreground;device.startup=true;
function tick(stamp){
  const cpuStart=performance.now(),frameMs=lastTime?stamp-lastTime:0;
  const dt=Math.min(.05,frameMs/1000);lastTime=stamp;
  if(!renderActivity.running||!renderActivity.foreground)return;
  if(entered&&document.getElementById('socialDialog')?.open)return;
  renderChangeGate.sample(camera.position.toArray(),camera.quaternion.toArray(),dt,!entered||Boolean(blend)||touring||keys.size>0);
  if(!renderChangeGate.ready)startupQuality.resetSamples();
  if(startupAutomatic&&renderChangeGate.ready&&entered&&!entryTransition&&!openingPreparing&&!blend&&!touring&&keys.size===0&&motionVelocity.length()<.15&&window.refugeBoot?.previewReady&&startupQuality.sample(frameMs,stamp,{targetFPS:Number($('targetFPS').value),gpuMs:renderBudget.gpuMs})){
    startupQuality.level=device.safe?0:2;device.startup=device.safe;
 const values=startupQuality.settings(desiredGraphics);for(const [id,value] of Object.entries(values))if(graphicsKeys.includes(id))$(id).value=value;
    device.startup=startupQuality.level===0;setQuality();$('world').dataset.startupTier=String(startupQuality.level);
    $('recommendStatus').textContent=startupQuality.level===2?'智能推荐已自动应用 · 60 帧目标、板书清晰保护，持续按实测性能调整。':'智能推荐已启用 · 正在逐步提升画质，优先保持流畅。';
    if(startupQuality.level===2)startupAutomatic=false;
  }
  frameQuality.sample(frameMs,stamp,{enabled:$('adaptiveQuality').value==='auto',targetFPS:Number($('targetFPS').value)});
  if(!entered){
    // Preview uses the actual opening camera; no room/board/physics updates before entry.
    updateRenderBudget(stamp);gpuTimer?.begin(stamp);
    retreat.setTime(sceneTime.hour,false,dt,1,sceneTime.date);
    retreat.ocean.material.uniforms.time.value+=dt;retreat.ocean.userData.study.update(camera,dt);
    try{if(profile.direct)renderer.render(scene,camera);else composer.render();window.refugeBoot?.preview();}finally{gpuTimer?.end();}
    // Keep entry and opening on one renderer; avoid video decode-to-WebGL handoff.
    return;
  }
  updateRoomVisibility(stamp);updateRenderBudget(stamp);
  // Include cloud/atmosphere targets as well as the final scene in GPU timing.
  weatherProbeFrame=!$('settings').hidden&&++weatherProbeCounter%3===0;
  const weatherSample=weatherTimer?.poll(stamp);if(weatherSample!=null){weatherGpuSamples.push(weatherSample);if(weatherGpuSamples.length>40)weatherGpuSamples.shift();weatherGpuMs=weatherGpuSamples.reduce((a,b)=>a+b,0)/weatherGpuSamples.length;}
  if(!weatherProbeFrame&&($('adaptiveQuality').value==='auto'||performanceMonitor.visible||!$('settings').hidden))gpuTimer?.begin(stamp);
  rooms.forEach(room=>room.update(room.renderActive?dt:Math.min(60,frameMs/1000),reduced.matches));
  retreat?.campus.automaticDoors.update(dt,reduced.matches,blend?.openingPath?[camera.position,new THREE.Vector3(...blend.openingPath.sample(blend.elapsed+1.2))]:[camera.position]);
  const remaining=openingCameraLock.remaining(stamp);
  if(remaining)controls.enabled=false;else if($('world').dataset.cameraLocked==='true')controls.enabled=true;
  movementHud.hint(remaining,dt);
  if(remaining)$('mode').textContent='开场运镜';else if($('world').dataset.cameraLocked==='true')updateLabels();
  $('world').dataset.cameraLocked=String(remaining>0);
  if(touring){
    if(!blend){const state=advanceShot(shot,time,dt,Number($('speed').value));time=state.time;if(shot!==state.index){shot=state.index;beginTransition();updateLabels();}}
    applyShot(dt);
  }else if(blend){
    applyShot(dt);
  }else if(SHOTS[shot].hallOrbit&&!free&&!speakerView&&!reduced.matches){
    time=(time+dt)%100;applyShot(dt);
  }else if(SHOTS[shot].walk&&!free){
    time=Math.min(SHOTS[shot].duration,time+dt);applyShot(dt);
    if(time===SHOTS[shot].duration){free=true;updateLabels();}
  }else if(!speakerView&&SHOTS[shot].lecture&&lecture&&boardFollow.following&&lecture.followEnabled){
    // Board tracking belongs to the teaching chapter, independently of touring.
    applyShot(reduced.matches?0:dt);
  }else{
    const forward=new THREE.Vector3();camera.getWorldDirection(forward);forward.y=0;forward.normalize();
    const right=new THREE.Vector3().crossVectors(forward,new THREE.Vector3(0,1,0));
    const velocity=keyboardMotion.update(keys,dt,Math.max(0,camera.position.y-(retreat?.ocean.material.uniforms.oceanLevel.value??0)));
    const move=forward.multiplyScalar(velocity.forward*dt).addScaledVector(right,velocity.right*dt);move.y+=velocity.up*dt;
    const yaw=velocity.yaw*dt;
    if(yaw){const direction=controls.target.clone().sub(camera.position).applyAxisAngle(new THREE.Vector3(0,1,0),yaw);controls.target.copy(camera.position).add(direction);if(SHOTS[shot].lecture)boardFollow.touch();}
    if(move.lengthSq()){if(SHOTS[shot].lecture)boardFollow.touch();camera.position.add(move);controls.target.add(move);}
    // Keep free-flight away from the clipping plane and terrain basement.
    controls.update();
  }
  if(stamp-lastUIStamp>=100){
    lastUIStamp=stamp;updateRegionDistance();
    if(lecture){updateLectureUI();reader?.update();}
    if(!speakerView&&SHOTS[shot].lecture&&lecture){
      $('mode').textContent=reportProgress||reportLoadError||(choosingReport?(lecture.navigation?.sections?'选择本次小节':'选择报告人 / 主题'):!lecture.followEnabled?'自由观察':boardFollow.following?'跟随当前板书':`自由观察 · ${Math.ceil(boardFollow.remaining)} 秒后跟随`);
      $('world').dataset.boardFollow=!lecture.followEnabled?'disabled':boardFollow.following?'following':'manual';
      $('world').dataset.board=String(lecture.clock.active);
    }else delete $('world').dataset.boardFollow;
    roomLecterns.forEach((lectern,i)=>{if(roomViews[i]?.consoleVisible)lectern.update({playing:rooms[i].playing,...rooms[i].progress,seeking:rooms[i].seeking,retractable:rooms[i].retractable,stored:rooms[i].stored,storageProgress:reduced.matches?(rooms[i].stored?1:0):rooms[i].storageProgress});});
    $('world').dataset.camera=camera.position.toArray().map(x=>x.toFixed(3)).join(',');
    $('world').dataset.transition=blend?'moving':'settled';$('world').dataset.opening=opening?'overview':'complete';
    const prior=SHOTS.slice(0,shot).reduce((a,s)=>a+s.duration,0);
    $('timelineFill').style.transform=`scaleX(${(prior+time)/totalDuration})`;
    $('world').dataset.shot=String(shot);
    updateSceneTime();
  }
  screenWebview.update(camera,rooms[0],scene);retreat.setMediaOpen(screenWebview.isOpen);const sunset=eventHours().sunset;retreat.campus.swivelChairs.setSunsetDirection(geographicDirectionToCampus(solarState(sunset,sceneTime.date).direction),visualHour>=sunset-2&&visualHour<=sunset+.5);retreat.campus.swivelChairs.update(dt);retreat.campus.lecternLift?.update(dt);if(retreat.campus.lecternLift?.moving)renderer.shadowMap.needsUpdate=true;$('lecternButton').disabled=activeRoom===0&&Boolean(retreat.campus.lecternLift?.lowered);
  retreat.residence.update(camera,retreat.sky.material.uniforms.day.value);
  const nearResidence=camera.position.distanceTo(retreat.residence.root.position)<180;
  const hallCenter=new THREE.Vector3(39*BUILDING_SCALE,3,0).add(buildingOffset('01B')),nearHall=camera.position.distanceTo(hallCenter)<65;
  const lightTarget=nearResidence?retreat.residence.root.position:nearHall?hallCenter:campusLightTarget;
  const shadowCamera=retreat.sun.shadow.camera,extent=nearResidence?65:nearHall?40:55*BUILDING_SCALE;
  const previousLightTarget=retreat.sun.target.position.clone();
  retreat.sun.target.position.lerp(lightTarget,1-Math.exp(-dt*2));
  if(Math.abs(shadowCamera.right-extent)>.01){Object.assign(shadowCamera,{left:-extent,right:extent,top:extent,bottom:-extent});shadowCamera.updateProjectionMatrix();renderer.shadowMap.needsUpdate=true;}
  if(previousLightTarget.distanceToSquared(retreat.sun.target.position)>.000001)renderer.shadowMap.needsUpdate=true;
  const weatherStart=performance.now();if(weatherProbeFrame)weatherTimer?.begin(stamp);
  try{updateAtmosphere(dt);}finally{if(weatherProbeFrame)weatherTimer?.end();}weatherCpuMs=performance.now()-weatherStart;
  constrainAboveWater(camera,controls.target,retreat?.ocean.material.uniforms.oceanLevel.value??seaLevel*BUILDING_SCALE);
  if(motionSample){const opacity=hallPassageMask.update(previousPosition.toArray(),camera.position.toArray(),cameraProbeRadius(camera.near,camera.fov,camera.aspect),dt);$('transition').style.opacity=String(opacity);$('world').dataset.cameraPassage=opacity.toFixed(3);}
  if(frameQuality.level<2&&$('rainEffects').value==='on')retreat.rain.update(dt,camera,retreat.weather,retreat.sky.material.uniforms.day.value,reduced.matches);else{retreat.rain.mesh.visible=false;retreat.ocean.material.uniforms.rainAmount.value=0;}
  syncRoomControls();
  if(motionSample&&dt>0){motionVelocity.subVectors(camera.position,previousPosition).divideScalar(dt);motionAcceleration.subVectors(motionVelocity,previousVelocity).divideScalar(dt);}
  movementHud.update(motionSample?Math.hypot(motionVelocity.x,motionVelocity.z):0,dt,!remaining&&!blend&&!touring&&!(SHOTS[shot].walk&&!free)&&!(SHOTS[shot].lecture&&lecture?.followEnabled&&boardFollow.following),Math.max(0,camera.position.y-(retreat?.ocean.material.uniforms.oceanLevel.value??0)));
  previousPosition.copy(camera.position);previousVelocity.copy(motionVelocity);motionSample=true;
  if(!reduced.matches){retreat.ocean.material.uniforms.time.value+=dt;retreat.landscape.update(dt);retreat.fleet.update(dt,retreat.ocean.material.uniforms.oceanLevel.value);}
  oceanBudget.sample(frameMs,stamp,{active:!document.hidden,eligible:renderChangeGate.ready&&teachingRoomAt(camera.position)<0,gpuMs:renderBudget.gpuMs});applyOceanQuality();
  retreat.ocean.userData.study.update(camera,dt);
  $('coastReadout').textContent='曲线坐标 ('+$('world').dataset.coastCoordinates+') km · 当前潮位 '+$('world').dataset.coastTide+' m';surfAudio.update(camera.position,retreat.ocean.material.uniforms.time.value,dt);
  try{if(profile.direct)renderer.render(scene,camera);else composer.render();}finally{gpuTimer?.end();}
  performanceMonitor.frame(stamp,frameMs,performance.now()-cpuStart,renderer,{gpuSupported:gpuTimer?.supported,ratio:renderer.getPixelRatio(),rooms:rooms.filter(room=>room.renderActive).length,adaptive:$('adaptiveReadout').textContent});
  if(frameMs>0&&frameMs<250){frameSamples.push(frameMs);cpuSamples.push(performance.now()-cpuStart);if(frameSamples.length>120){frameSamples.shift();cpuSamples.shift();}}
  if(stamp-metricsAt>1000&&frameSamples.length>20){metricsAt=stamp;if(!$('settings').hidden){$('weatherCost').textContent='云 / 大气预计算 GPU '+(weatherGpuMs==null?'待采样':weatherGpuMs.toFixed(2)+' ms')+' · CPU '+weatherCpuMs.toFixed(2)+' ms · 云 '+({low:'标准',medium:'精细',high:'超精细',off:'关闭'}[activeCloudQuality])+'（不含主画面的天空、水面和雨滴）';$('world').dataset.weatherCost=JSON.stringify({prepassGPU:weatherGpuMs,prepassCPU:weatherCpuMs,cloud:activeCloudQuality});}const frames=[...frameSamples].sort((a,b)=>a-b),cpu=[...cpuSamples].sort((a,b)=>a-b);$('world').dataset.performance=JSON.stringify({frameP50:frames[Math.floor(frames.length*.5)],frameP95:frames[Math.floor(frames.length*.95)],cpuP95:cpu[Math.floor(cpu.length*.95)],calls:renderer.info.render.calls,triangles:renderer.info.render.triangles,direct:profile.direct,renderScale,gpuMs:renderBudget.gpuMs,gpuTiming:gpuTimer?.supported,adaptiveLevel:frameQuality.level,adaptiveFPS:frameQuality.stats?.fps});if(blend)$('world').dataset.transitionPerformance=$('world').dataset.performance;}

}
let startupPaintAt=0;
async function paintStartup(percent,label){
 await window.refugeBoot?.waitForEntryUI?.();
 reportSceneProgress(percent,label);
 await new Promise(resolve=>setTimeout(resolve,16));
 if(retreat&&renderActivity.foreground){
  const now=performance.now(),dt=startupPaintAt?Math.min(.1,(now-startupPaintAt)/1000):1/60;startupPaintAt=now;
  retreat.setTime(sceneTime.hour,false,dt,1,sceneTime.date);
  retreat.ocean.userData.study.update(camera,0);renderer.render(scene,camera);window.refugeBoot?.preview();
 }
 await new Promise(resolve=>setTimeout(resolve,16));
}

function reportSceneProgress(value,label){window.refugeBoot?.stage(value<20?value:24+(value-20)*.68,label);}
const weatherService=createShanghaiWeather({onChange(value,state){weatherReading=value;weatherStatus=state;weatherLabel();updateSunEvents();if($('weatherMode').value==='live')retreat?.setWeather(value);}});

try{
  reportSceneProgress(10,'准备画面');
  renderer=new THREE.WebGLRenderer({canvas:$('world'),alpha:true,antialias:!device.mobile,powerPreference:device.mobile?'default':'high-performance'});
  $('world').addEventListener('webglcontextlost',event=>{event.preventDefault();gpuTimer?.dispose();weatherTimer?.dispose();fail(new Error('WebGL context lost'));});
  renderer.debug.onShaderError=()=>fail(new Error('当前设备无法编译场景效果，请尝试低负载模式。'));
  gpuTimer=createGpuTimer(renderer.getContext());weatherTimer=createGpuTimer(renderer.getContext(),137);detectGraphics();device.gpuTiming=gpuTimer.supported;
  nativeSamples=renderer.getContext().getParameter(renderer.getContext().SAMPLES);
  renderer.outputColorSpace=THREE.SRGBColorSpace;renderer.toneMapping=THREE.ACESFilmicToneMapping;renderer.toneMappingExposure=.78;
  renderer.shadowMap.enabled=false;renderer.shadowMap.type=THREE.PCFSoftShadowMap;
  renderer.shadowMap.autoUpdate=false;renderer.shadowMap.needsUpdate=true;
  camera=new THREE.PerspectiveCamera(49,innerWidth/innerHeight,.2,12000);
  controls=new OrbitControls(camera,$('world'));cameraInput=configureCameraInput(controls,$('world'));
  cameraIntent=bindCameraIntent(document,$('world'),()=>{if(!controls.enabled)return;stopTour();if(SHOTS[shot].lecture&&cameraIntent.hasManualPointers())boardFollow.begin();});
  controls.minDistance=.4;controls.maxDistance=14000;controls.maxPolarAngle=Math.PI*.94;controls.enablePan=true;
  controls.addEventListener('change',()=>constrainAboveWater(camera,controls.target,retreat?.ocean.material.uniforms.oceanLevel.value??seaLevel*BUILDING_SCALE));
  controls.autoRotate=false;
  controls.addEventListener('start',()=>{if(cameraIntent.hasPointers()&&!cameraIntent.hasManualPointers())return;stopTour();if(SHOTS[shot].lecture)boardFollow.begin();});
  controls.addEventListener('end',()=>{if(SHOTS[shot].lecture&&boardFollow.interacting)boardFollow.end();});
  window.addEventListener('blur',()=>{if(boardFollow.interacting)boardFollow.end();});
  $('world').addEventListener('pointercancel',()=>{if(boardFollow.interacting)boardFollow.end();});
  camera.position.fromArray(OPENING_POSE.position);controls.target.fromArray(OPENING_POSE.target);camera.fov=openingFrameFov(camera.aspect);camera.updateProjectionMatrix();controls.update();
  resize();
  const environment=await createArrivalEnvironment(renderer,scene,value=>reportSceneProgress(value,'准备海面'),device,{hour:sceneTime.hour,date:sceneTime.date,weather:weatherReading});
  environment.study.update(camera,0);renderer.render(scene,camera);window.refugeBoot?.preview();
  window.refugeBoot?.stage(18,'天气数据');await weatherService.ready;
  const startupWeather=weatherReading?{...weatherReading}:{cloud:.14,rain:0,fog:0,wind:8,windDirection:225};
  // Resolve the actual sky before architecture; no input gesture is required.
  const skyUniforms=environment.sky.material.uniforms,waterUniforms=environment.ocean.material.uniforms;
  skyUniforms.cloud.value=startupWeather.cloud*twilightCloudFactor(sceneTime.hour,solarEvents(sceneTime.date));
  const cloudStorm=Math.max(0,Math.min(1,(skyUniforms.cloud.value-.4)/.6));skyUniforms.storm.value=cloudStorm*cloudStorm*(3-2*cloudStorm);
  let earlyPaintAt=performance.now();
  function paintEnvironment(){
    const now=performance.now(),dt=Math.min(.1,(now-earlyPaintAt)/1000);earlyPaintAt=now;
    environment.sky.userData.updateAtmosphere(dt);
    for(const [key,source] of Object.entries({skyMap:'atmosphereMap',skyPrevious:'atmosphereMapPrevious',skyBlend:'atmosphereBlend',skyPhysical:'useAtmosphere',skyCloudMap:'cloudMap',skyCloudPrevious:'cloudMapPrevious',skyCloudBlend:'cloudBlend',skyCloudEnabled:'useVolumeClouds'}))waterUniforms[key].value=skyUniforms[source].value;
    environment.study.update(camera,dt);renderer.render(scene,camera);window.refugeBoot?.preview();
  }
  environment.sky.userData.setCloudQuality($('cloudQuality').value);
  await environment.sky.userData.prepareClouds(value=>{window.refugeBoot?.stage(18+value*6,'天空与海面倒影');paintEnvironment();});

  await new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)));
  await window.refugeBoot?.waitForEntryUI?.();
  retreat=await withDeadline(createRetreat(renderer,scene,value=>{if(typeof value==='number')reportSceneProgress(value,'构建空间');paintEnvironment();},device,{hour:sceneTime.hour,date:sceneTime.date,weather:startupWeather,environment}),45000,'空间材质加载');
  retreat.setWeather(startupWeather,true);setQuality();
  await paintStartup(66,'准备报告厅');
  const lectureRoot=new THREE.Group();lectureRoot.name='East-facing compact auditorium blackboards';configureLectureRoot(lectureRoot);scene.add(lectureRoot);
  lecture=await withDeadline(createLecture(lectureRoot,renderer,{onProgress:value=>reportSceneProgress(66+value*5,'准备报告厅'),floorMaterial:retreat.campus.carpetMaterial,isActive:()=>renderActivity.foreground,retractable:true,requireSelection:true,defaultReport:'ye',boardScale:device.boardScale,writingStyle:boardWritingStyle}),30000,'报告板书加载');retreat.roomFill.apply(lectureRoot);
  await withDeadline(lecture.prepareOpening(value=>reportSceneProgress(71+value*3,'准备板书')),30000,'开场板书加载');openingPrepared=true;
  rooms.push(lecture);
  roomLecterns.push(retreat.campus.lectern,...retreat.campus.discussion.lecterns);
  for(let level=0;level<3;level++){
    await paintStartup(74+level*4,'准备讨论教室 '+(level+1));
    const root=new THREE.Group();root.name='Discussion classroom blackboards '+(level+1);configureSeminarRoot(root,level);scene.add(root);
    const room=await createLecture(root,renderer,level===0?{isActive:()=>renderActivity.foreground,boardScale:device.boardScale,writingStyle:boardWritingStyle,highlight:$('boardHighlight').value!=='off',reports:[KM_REPORT],defaultReport:'km',viewScale:.52,requireSelection:true,hideBoardHeadings:true}:{boardScale:device.boardScale,disabled:true,viewScale:.52,hideBoardHeadings:true});
    room.playing=false;retreat.roomFill.apply(root);rooms.push(room);
  }
  await paintStartup(88,'整理空间');
  finishCampusLayout(scene,retreat,rooms);
  rooms.forEach((room,i)=>{
    room.root.updateWorldMatrix(true,true);
    const bounds=new THREE.Box3(new THREE.Vector3(13.8,-.6,-11.5),new THREE.Vector3(36.6,5.3,-9.6)).applyMatrix4(room.root.matrixWorld);
    roomViews.push({bounds,consoleBounds:new THREE.Box3().setFromObject(roomLecterns[i].group),consoleVisible:false,visible:false,floor:(i?seminarFloor(i-1):DECK_Y)*BUILDING_SCALE,height:i?3.8:4.9});
    room.setRenderActive(false);roomLecterns[i].setScreenEnabled(false);
  });
  reader=createChalkReader(new Proxy({}, {get:(_,key)=>lecture[key]}));
  buildSeminarNavigation();
  installPhysicalControls();
  populateReport();
  if(reduced.matches){lecture.playing=false;lecture.staticPage();}
  if(!profile.direct){composer=new EffectComposer(renderer);composer.addPass(new RenderPass(scene,camera));
  bloom=new UnrealBloomPass(new THREE.Vector2(innerWidth,innerHeight),0,.25,1.6);bloom.enabled=false;composer.addPass(bloom);composer.addPass(new OutputPass());}
  window.refugeBoot?.stage(70.3,'材质纹理');await startDeferredTextures(value=>window.refugeBoot?.stage(70.3+value*5.7,'材质纹理'));window.refugeBoot?.stage(78,'材质就绪');
  retreat.setWeather(startupWeather,true);setQuality();updateSceneTime();retreat.setTime(sceneTime.hour,false,0,1,sceneTime.date);updateLabels();camera.position.fromArray(OPENING_POSE.position);controls.target.fromArray(OPENING_POSE.target);controls.update();$('transition').style.opacity=0;
  // Hold the already rendered live frame while calibration reallocates GPU buffers.
  renderer.render(scene,camera);
  const arrivalHold=document.createElement('canvas');arrivalHold.id='arrivalRenderHold';
  arrivalHold.width=renderer.domElement.width;arrivalHold.height=renderer.domElement.height;
  arrivalHold.setAttribute('aria-hidden','true');arrivalHold.getContext('2d').drawImage(renderer.domElement,0,0);
  document.body.append(arrivalHold);
  await retreat.prepareRendering((value,label)=>window.refugeBoot?.stage(78+value*10,label));
  window.refugeBoot?.stage(88,'场景材质');
  await new Promise(resolve=>setTimeout(resolve,0));
  // Compile materials before camera motion, rather than at a cached-video handoff.
  if(renderer.compileAsync){
    const compiling=renderer.compileAsync(scene,camera);
    const progressTimer=setInterval(()=>{const programs=renderer.info.programs||[];if(programs.length)window.refugeBoot?.stage(88+2*programs.filter(p=>p.isReady()).length/programs.length,'场景材质');},80);
    try{await compiling;}finally{clearInterval(progressTimer);}
  }
  window.refugeBoot?.stage(92,'天气与反射就绪');
  window.refugeBoot?.stage(94,'云层与水面倒影');
  // Cloud panorama was prepared once with the selected quality.

  retreat.setTime(sceneTime.hour,false,0,1,sceneTime.date);
  window.refugeBoot?.stage(96,'阴影与反射');renderer.shadowMap.needsUpdate=true;
  await renderer.compileAsync?.(scene,camera);
  for(let i=0;i<3;i++){
    retreat.ocean.userData.study.update(camera,0);
    if(profile.direct)renderer.render(scene,camera);else composer.render();
    await new Promise(resolve=>setTimeout(resolve,16));
  }
  // Warm both sides of the hall before motion, with the same readable framebuffer.
  const savedCamera={position:camera.position.clone(),rotation:camera.quaternion.clone(),fov:camera.fov};
  const hallOffset=buildingOffset('01B'),focus=lecture.reportFocus();
  const hallEye=new THREE.Vector3(SEAT_ROWS[1].x*BUILDING_SCALE+hallOffset.x-.65,(DECK_Y+.028)*BUILDING_SCALE+SEAT_ROWS[1].rise+1.65,hallOffset.z);
  const warmViews=[{eye:hallEye,target:focus},{eye:new THREE.Vector3(HALL.east*BUILDING_SCALE+hallOffset.x+25,hallEye.y,hallOffset.z),target:hallEye}];
  try{
    for(let i=0;i<warmViews.length;i++){
      camera.position.copy(warmViews[i].eye);camera.lookAt(warmViews[i].target);camera.updateMatrixWorld();
      retreat.ocean.userData.study.update(camera,0);await renderer.compileAsync?.(scene,camera);
      for(let frame=0;frame<2;frame++){if(profile.direct)renderer.render(scene,camera);else composer.render();await new Promise(resolve=>setTimeout(resolve,16));}
      window.refugeBoot?.stage(96.5+(i+1)*.25,'报告厅视角预热');
    }
  }finally{camera.position.copy(savedCamera.position);camera.quaternion.copy(savedCamera.rotation);camera.fov=savedCamera.fov;camera.updateProjectionMatrix();camera.updateMatrixWorld();retreat.ocean.userData.study.update(camera,0);}
  window.refugeBoot?.stage(98,'首帧就绪');
  // Preserve prepared effects and the opening camera; never clear and replay them.
  retreat.sky.material.uniforms.cloudOrigin.value.copy(camera.position).multiplyScalar(.001);
  retreat.sky.material.uniforms.cloudOrigin.value.y=Math.max(.001,retreat.sky.material.uniforms.cloudOrigin.value.y);
  retreat.setTime(sceneTime.hour,false,1/60,1,sceneTime.date);
  retreat.ocean.userData.study.update(camera,0);
  if(profile.direct)renderer.render(scene,camera);else composer.render();
  arrivalHold.remove();
  startupAutomatic=false;frameQuality.resetSamples();oceanBudget.resetSamples();
  $('world').dataset.graphicsMode='smart';$('recommendStatus').textContent=device.safe?'低负载模式 · 保留板书清晰度':'智能推荐已默认应用 · 60 帧预算、文字保护、运行中自动调整环境效果';
  // Keep normal frustum culling: never allocate/render the entire campus at startup.
  if(failed||renderer.getContext().isContextLost())throw new Error('WebGL context lost');
  if(renderActivity.foreground){if(profile.direct)renderer.render(scene,camera);else composer.render();window.refugeBoot?.preview();}
  if(failed)throw new Error('场景效果未能加载，请尝试低负载模式。');
  clearTimeout(window.refugeLoadingTimer);$('error').hidden=true;$('world').dataset.ready='true';$('world').dataset.entered='false';
  window.refugeBoot?.ready();$('world').dataset.startupTier=String(startupQuality.level);renderActivity.setEnabled(!failed);
  if($('loading').dataset.entryRequested==='true')enterScene();
  // Fetch only manifests and covers in the background, without delaying entry.

}catch(error){document.getElementById('arrivalRenderHold')?.remove();fail(error);}

$('tour').addEventListener('click',()=>{
  if(!renderer||!retreat||!cameraIntent.canActivate())return;
  if(touring){opening=null;touring=false;blend=null;$('transition').style.opacity=0;updateLabels();}else resumeTour();
});
document.querySelectorAll('#chapters button[data-shot]').forEach(button=>button.addEventListener('click',()=>{
  if(!retreat||!cameraIntent.canActivate())return;
  const index=Number(button.dataset.shot);
  if(SHOTS[index].name==='报告厅')activateRoom(0,false);
  selectShot(index);
}));
function showSettings(open){
 if(open)closeTime();
 $('settings').hidden=!open;$('settingsButton').setAttribute('aria-expanded',String(open));
}
$('settingsButton').addEventListener('click',()=>showSettings($('settings').hidden));
$('quality').addEventListener('change',()=>{if(retreat&&GRAPHICS_PRESETS[$('quality').value])applyGraphics(GRAPHICS_PRESETS[$('quality').value]);});
$('settingsClose').addEventListener('click',()=>showSettings(false));
$('recommendGraphics').addEventListener('click',()=>{applyGraphics(recommendedGraphics({mobile:device.mobile,gpu:gpuName,maxTextureSize:renderer.capabilities.maxTextureSize}));$('world').dataset.graphicsMode='smart';$('recommendStatus').textContent='智能推荐已应用 · 60 帧预算、文字保护、自动调整渲染精度。';});
for(const id of graphicsKeys.filter(k=>!['quality','adaptiveQuality'].includes(k)))$(id).addEventListener('change',()=>{if(retreat){markManualGraphics();startupAutomatic=false;device.startup=false;$('quality').value='custom';setQuality();saveGraphics();weatherGpuSamples=[];weatherGpuMs=null;}});
$('waveStrength').addEventListener('input',()=>{$('waveStrengthValue').textContent=$('waveStrength').value+'%';});
$('resolutionScale').addEventListener('input',()=>{$('resolutionValue').textContent=$('resolutionScale').value+'%';});
$('boardHighlight').addEventListener('change',()=>{rooms.forEach(room=>room.setHighlight($('boardHighlight').value!=='off'));try{localStorage.setItem('refuge-board-highlight',$('boardHighlight').value);}catch{}});
$('boardClarity').addEventListener('change',()=>{rooms.forEach(room=>room.setClarity($('boardClarity').value));try{localStorage.setItem('refuge-board-clarity',$('boardClarity').value);}catch{}});
try{if(localStorage.getItem('refuge-board-clarity')==='natural')$('boardClarity').value='natural';}catch{}
$('adaptiveQuality').addEventListener('change',()=>{if(retreat){markManualGraphics();startupAutomatic=false;device.startup=false;frameQuality.reset();renderBudget.reset();updateRenderBudget(performance.now());saveGraphics();}});
$('boardFollowDelay').addEventListener('input',event=>{boardFollow.setDelay(event.target.value);$('boardFollowDelayValue').textContent=boardFollow.delay+' 秒';});
$('boardWritingStyle').addEventListener('change',async event=>{const select=event.target,prior=boardWritingStyle;boardWritingStyle=select.value;select.disabled=true;$('boardWritingStyleStatus').textContent='正在切换书写样式…';try{await Promise.all(rooms.map(room=>room.setWritingStyle(boardWritingStyle)));try{localStorage.setItem('refuge-board-writing-style',boardWritingStyle);}catch{}$('boardWritingStyleStatus').textContent=boardWritingStyle==='refined'?'字母、数字及已支持符号按人工笔顺书写；中文和其余符号保留原字形。':'Marck Script（舒展）· 原来的非笔顺显现方式。';}catch(error){boardWritingStyle=prior;select.value=prior;await Promise.allSettled(rooms.map(room=>room.setWritingStyle(prior)));$('boardWritingStyleStatus').textContent='切换未完成，已恢复原样式。';console.error(error);}finally{select.disabled=false;}});
$('writingSpeed').addEventListener('input',event=>{const value=Number(event.target.value);lecture?.setWritingSpeed(value);$('writingSpeedValue').textContent=value+' ×';});
$('rotationSensitivity').addEventListener('input',event=>cameraInput?.set(event.target.value));
$('light').addEventListener('input',()=>{if(retreat){hallSunRamp=null;sunriseIntro.cancel();timePresentation.seek();sceneTime.previewAt(Number($('light').value));}});
$('clockPlay').addEventListener('click',()=>{hallSunRamp=null;sunriseIntro.cancel();timePresentation.seek();sceneTime.setRate(1);$('timeRate').value='1';sceneTime.sync();updateSceneTime();});
function syncCloudControl(value){const percent=Math.round(Math.max(0,Math.min(1,value))*100);$('cloudCoverage').value=String(percent);$('cloudCoverageValue').textContent=percent+'%';$('cloudCoverage').setAttribute('aria-valuetext',percent+'%');}
$('cloudCoverage').addEventListener('input',()=>{const value=Number($('cloudCoverage').value)/100;$('weatherMode').value='custom';retreat?.setCloudCoverage(value);weatherLabel();});
function weatherLabel(){
 const mode=$('weatherMode').value;syncCloudControl(mode==='live'?(weatherReading?.cloud??.14):mode==='clear'?0:mode==='cloudy'?.8:mode==='rain'?1:Number($('cloudCoverage').value)/100);if(mode!=='live'){$('weatherSummary').textContent=mode==='clear'?'预览 · 晴天 · 无云无雨':mode==='cloudy'?'预览 · 多云':mode==='custom'?'自定义云量':'预览 · 雨天';$('weatherDetail').textContent='正在使用天气预览；选择上海实时天气可恢复实况。';return;}
 const label=weatherReading?`${weatherReading.label} · ${Math.round(weatherReading.temperature)}°C`:'天气暂不可用';
 
 $('weatherSummary').textContent='上海 · '+(weatherStatus==='loading'?'正在获取天气':label)+(weatherStatus==='cached'?'（缓存）':'');
 $('weatherDetail').textContent=weatherReading?`云量 ${Math.round(weatherReading.cloud*100)}% · 风速 ${weatherReading.wind} km/h · ${Number.isFinite(weatherReading.windDirection)?weatherReading.windDirection+'° 来风':'风向暂无'}（10 m 风近似驱动云层） · 降水 ${weatherReading.rain} mm · 日出 ${weatherReading.sunrise} / 日落 ${weatherReading.sunset} · 数据 ${weatherReading.time?.slice(11,16)||'—'}`:'连接不可用时使用晴朗天空预设；不会把预设当作实况。';
}
function formatHour(h){const m=Math.floor(h*60);return String(Math.floor(m/60)%24).padStart(2,'0')+':'+String(m%60).padStart(2,'0');}

function closeTime(){ $('timePanel').hidden=true;$('timeButton').setAttribute('aria-expanded','false'); }
$('timeClose').addEventListener('click',closeTime);
$('timeButton').addEventListener('click',()=>{const open=$('timePanel').hidden;showSettings(false);$('timePanel').hidden=!open;$('timeButton').setAttribute('aria-expanded',String(open));updateSunEvents();});
function eventHours(){const fallback=solarEvents(sceneTime.date);const parse=(text,otherwise)=>/^\d{2}:\d{2}$/.test(text||'')?Number(text.slice(0,2))+Number(text.slice(3))/60:otherwise;return sceneTime.dayOffset?fallback:{sunrise:parse(weatherReading?.sunrise,fallback.sunrise),sunset:parse(weatherReading?.sunset,fallback.sunset)};}
function updateSunEvents(){const times=eventHours();$('sunriseTime').textContent=formatHour(times.sunrise);$('sunsetTime').textContent=formatHour(times.sunset);$('sunEventSource').textContent=weatherReading?.sunrise?'上海今日 · 天气服务时刻':'上海今日 · 本地天文估算';}
$('timeRate').addEventListener('change',()=>{hallSunRamp=null;sunriseIntro.cancel();sceneTime.setRate($('timeRate').value);updateSceneTime();});
$('timeRun').addEventListener('click',()=>{sunriseIntro.cancel();if(sceneTime.playing)sceneTime.pause();else sceneTime.play($('timeRate').value);updateSceneTime();});
for(const [id,event] of [['playSunrise','sunrise'],['playSunset','sunset']])$(id).addEventListener('click',()=>{sunriseIntro.cancel();timePresentation.seek();sceneTime.previewAt(eventHours()[event]-.05);sceneTime.play($('timeRate').value);updateSceneTime();});
$('weatherMode').addEventListener('change',()=>{const v=$('weatherMode').value;weatherLabel();if(v==='custom'){retreat?.setCloudCoverage(Number($('cloudCoverage').value)/100);return;}retreat?.setWeather(v==='live'?weatherReading:v==='clear'?{cloud:0,rain:0,fog:0}:v==='cloudy'?{cloud:.8}:{cloud:1,rain:3});});
function updateSceneTime(){
 const motion=retreat?.cloudMotion;if(motion){const speed=motion.speed.toFixed(1),factor='· 时间影响 '+motion.multiplier.toFixed(2)+'×';if($('cloudSpeedValue').textContent!==speed)$('cloudSpeedValue').textContent=speed;if($('cloudSpeedFactor').textContent!==factor)$('cloudSpeedFactor').textContent=factor;}

 sceneTime.update();if(document.activeElement!==$('light'))$('light').value=String(sceneTime.hour);
 if(sunriseIntro.catchingUp||sunriseIntro.active){$('introCatchRate').textContent=`${sunriseIntro.active?'开场日出':'自动追时'} · ${sceneTime.rate.toFixed(1)}×`;$('timeRate').value='intro';}else if($('timeRate').value==='intro')$('timeRate').value=String(sceneTime.rate);
 $('timeButtonClock').textContent=formatHour(sceneTime.hour);$('timeRun').textContent=sceneTime.playing?'暂停时间':'播放时间';$('timeState').textContent=sunriseIntro.waiting?'开场运镜 · 时间 1×':sunriseIntro.active?`开场日出 · ${sceneTime.rate.toFixed(1)}× · 5 秒渐进至 30×`:sunriseIntro.catchingUp?`正在追至上海当前时间 · ${Math.round(sceneTime.rate)}×`:!sceneTime.preview?'与上海当前时间同步':sceneTime.playing?`时间流逝 · ${sceneTime.rate}×`:'时间预览 · 已暂停';const minutes=Math.floor(sceneTime.hour*60);$('sceneClock').textContent=String(Math.floor(minutes/60)).padStart(2,'0')+':'+String(minutes%60).padStart(2,'0');
 controlLabel($('clockPlay'),sceneTime.preview?'回到上海当前时间':'已同步上海时间');$('clockPlay').setAttribute('aria-pressed',String(!sceneTime.preview));
 $('world').dataset.clockMode=sceneTime.preview?'preview':'shanghai';$('world').dataset.hour=sceneTime.hour.toFixed(4);lecture?.setConsoleState();
}

function updateAtmosphere(dt){
 if(hallSunRamp!==null){if(!sceneTime.playing||!sceneTime.preview)hallSunRamp=null;else if(!blend){if(hallSunRamp===0&&SHOTS[shot].name==='报告厅看日出')retreat.fleet.startSunrisePass();hallSunRamp+=dt;sceneTime.setRate(sunViewRate(hallSunRamp));if(hallSunRamp>=5)hallSunRamp=null;}}
 if(sunriseIntro.update(dt))$('timeRate').value='1';sceneTime.update(dt);visualHour=timePresentation.update(sceneTime.hour,dt);$('timeFade').style.opacity=String(timePresentation.opacity);retreat.setTime(visualHour,false,dt,sceneTime.playing?sceneTime.rate:1,sceneTime.date);
 const angle=Math.abs(((visualHour-lastShadowHour+36)%24)-12);
 if(angle>.00028){renderer.shadowMap.needsUpdate=true;lastShadowHour=visualHour;}
 $('world').dataset.visualHour=(((visualHour%24)+24)%24).toFixed(4);
}

function populateReport(){
  $('lecturePage').replaceChildren();
  for(let i=lecture.clock.startAt;i<=lecture.clock.stopAt;i++){
    const option=document.createElement('option'),copy=lecture.copy(i);option.value=String(i);option.textContent=`${copy.source} · ${copy.title}`;$('lecturePage').append(option);
  }
  $('reportSelect').replaceChildren(...lecture.reports.map(report=>{const option=document.createElement('option');option.value=report.id;option.textContent=report.speaker+' · '+report.topic;return option;}));
  $('reportSelect').value=lecture.report.id;populateVoiceOptions();
  $('lectureHeading').textContent=lecture.report.speaker+' · '+lecture.report.topic;
  for(const id of ['lectureSource','readerSource']){$(id).href=lecture.report.url;$(id).textContent=lecture.report.sourceLabel+' ↗';}
  $('world').dataset.report=lecture.report.id;controlLabel($('reportButton'),lecture.navigation?.sections?'选择本次小节':'选择报告人和主题');
  $('lectureProgress').max=String(lecture.progress.total);$('lectureProgress').value=String(lecture.progress.page+1);
}
function populateVoiceOptions(){
 const selector=$('reportVoiceTone'),variants=lecture.report.narration?.voices||[];
 const choices=lecture.report.narration?[{id:'original',label:'沈腾参考音色 · 完整报告'},...variants.filter(v=>v.id!=='original'),{id:'off',label:'关闭语音 · 仅板书'}]:[{id:'off',label:'此报告暂无语音'}];
 selector.replaceChildren(...choices.map(item=>{const option=document.createElement('option');option.value=item.id;option.textContent=item.label;return option;}));selector.value=lecture.report.narration?lecture.voiceTone:'off';selector.disabled=!lecture.report.narration;updateVoicePreferences();
}
function updateVoicePreferences(){
 if(!lecture)return;const enabled=Boolean(lecture.report.narration),state=lecture.voiceState,selected=$('reportVoiceTone').value;
 $('reportVoiceLoad').disabled=!enabled||changingVoice||state.phase==='loading';$('reportVoiceLoad').textContent=changingVoice?'正在加载…':selected==='off'?'关闭语音':'加载音色';
 const manifest=lecture.voiceManifest,bytes=manifest?.chapters?.reduce((sum,c)=>sum+(c.bytes||0),0),size=bytes?(bytes/1e6).toFixed(2)+' MB':'';
 $('reportVoiceInfo').textContent=voiceLoadError||state.phase==='error'?(voiceLoadError||state.error):changingVoice||state.phase==='loading'?'语音加载 · '+(state.progress===null?'…':Math.round(state.progress*100)+'%'):!enabled?'此报告暂无录制语音。':!lecture.voiceEnabled?'语音已关闭；保留当前板书。':manifest?(manifest.voice+' · '+size+' · '+Math.floor(manifest.duration/60)+' 分 '+Math.floor(manifest.duration%60)+' 秒。AI 合成，按章节加载。'):'选择音色后按需加载，网页开场不下载报告音频。';
}
$('reportVoiceTone').addEventListener('change',updateVoicePreferences);
$('reportVoiceLoad').addEventListener('click',async()=>{
 if(!lecture||changingVoice)return;const target=lecture;changingVoice=true;voiceLoadError='';updateVoicePreferences();
 try{if(!await target.setVoiceTone($('reportVoiceTone').value))voiceLoadError=target.voiceState.error||'音色加载失败，请重试。';}catch(error){voiceLoadError=error.message;}finally{changingVoice=false;updateVoicePreferences();updateLectureUI();}
});
let changingLanguage=false,changingReport=false,reportLoadError='',reportProgress='',reportRequest=0;
async function switchReport(id,{autoplay=false}={}){
  if(!lecture||changingLanguage)return;
  const request=++reportRequest;changingReport=true;reportLoadError='';voiceLoadError='';
  $('reportSelect').value=id;
  reportProgress='正在切换至 '+$('reportSelect').selectedOptions[0].textContent+'…';
  $('lectureStatus').textContent=reportProgress;$('mode').textContent=reportProgress;
  $('reportSelect').setAttribute('aria-busy','true');
  try{const targetLecture=lecture;if(!await targetLecture.setReport(id,{autoplay})||request!==reportRequest||lecture!==targetLecture)return;populateReport();if(reduced.matches){if(!autoplay)lecture.playing=false;lecture.staticPage();}reader?.close();selectShot(0);}
  catch(error){if(request!==reportRequest)return;reportLoadError=error.message;$('lectureStatus').textContent=error.message;$('reportSelect').value=lecture.report.id;populateVoiceOptions();$('mode').textContent=error.message;}
  finally{if(request===reportRequest){changingReport=false;reportProgress='';$('reportSelect').setAttribute('aria-busy','false');}}
}
$('reportButton').addEventListener('click',()=>{if(!lecture||!cameraIntent.canActivate())return;$('lecturePanel').hidden=true;$('lectureButton').setAttribute('aria-expanded','false');lecture.screenAction('screen:report');selectShot(0,true);reader?.close();});
$('reportSelect').addEventListener('change',event=>switchReport(event.target.value));
async function switchChalkLanguage(){
  if(!lecture||changingLanguage||changingReport)return;changingLanguage=true;
  try{await lecture.setLanguage(lecture.language==='zh'?'en':'zh');
    for(const option of $('lecturePage').options){const copy=lecture.copy(Number(option.value));option.textContent=`${copy.source} · ${copy.title}`;}reader?.update();
  }catch(error){$('lectureStatus').textContent=error.message;}finally{changingLanguage=false;}
}
function installPhysicalControls(){
  const ray=new THREE.Raycaster(),pointer=new THREE.Vector2();
  const hit=e=>{
    const rect=$('world').getBoundingClientRect();pointer.set((e.clientX-rect.left)/rect.width*2-1,1-(e.clientY-rect.top)/rect.height*2);
    scene.updateMatrixWorld(true);camera.updateMatrixWorld(true);ray.setFromCamera(pointer,camera);
    ray.far=15;const candidate=ray.intersectObjects([...retreat.campus.automaticDoors.targets,...retreat.campus.swivelChairs.targets,...(physicalRoom===activeRoom?[...lecture.hoverTargets.filter(t=>t.visible&&lecture.root.visible),...roomLecterns[activeRoom].targets]:[])],false)[0];$('world').dataset.physicalHit=candidate?.object.name||'';$('world').dataset.physicalBlock='';if(!candidate||candidate.distance>15)return null;
    // Ignore transparent glazing, but opaque roof/walls must block a press.
    for(const h of (ray.far=candidate.distance,ray.intersectObjects(scene.children.filter(o=>o.visible),true))){
      if(h.distance>=candidate.distance-.015)break;
      let visible=true;for(let p=h.object;p;p=p.parent)if(!p.visible)visible=false;
      if(!visible||h.object.parent===candidate.object||h.object===candidate.object)continue;
      const material=h.object.material;if(material?.transparent&&material.opacity<.5)continue;
      if(h.object.isMesh){$('world').dataset.physicalBlock=h.object.name+' | '+h.object.material?.type;return null;}
    }
    if(retreat.campus.swivelChairs.targets.includes(candidate.object)){candidate.object.userData.action='chair:turn:'+candidate.instanceId;candidate.object.userData.label='旋转座椅';}
    candidate.object.userData.action=physicalHitAction(candidate,lecture.clock);$('world').dataset.physicalAction=candidate.object.userData.action||'';
    return candidate.object;
  };
  $('world').addEventListener('pointermove',()=>lecture?.screenWake?.(),{passive:true});
  bindPhysicalButtons($('world'),controls,hit,action=>{
    if(action.startsWith('chair:turn:'))retreat.campus.swivelChairs.turn(Number(action.split(':')[2]));
    else if(action.startsWith('screen:site:')){const site=VIDEO_SITES.find(s=>s.id===action.slice(12));if(site)screenWebview.open(site);}
    else if(action.startsWith('screen:')){lecture.screenAction(action);updateLectureUI();}
    else if(action==='lectern:view')enterSpeakerView();
    else if(action==='lectern:stow')$('boardStorage').click();
    else if(action==='lectern:play')$('lecturePlay').click();
    else if(action==='lectern:previous')$('lecturePrevious').click();
    else if(action==='lectern:next')$('lectureNext').click();
    else if(action.startsWith('page:seek:'))seekLecture(Number(action.split(':')[2]));
    else if(action.startsWith('seminar:section:'))selectSeminarPart(lecture.navigation.sections.find(s=>s.id===action.split(':')[2]));
    else if(action.startsWith('seminar:'))lecture.screenAction(action);
    else if(action==='voice:toggle')$('lecturePlay').click();
    else if(action==='camera:toggle'){lecture.autoCamera=!lecture.autoCamera;if(lecture.autoCamera){boardFollow.reset();focusLecture();}else stopTour();updateLectureUI();}
    else if(action==='language')switchChalkLanguage();
    else if(action.startsWith('report:'))switchReport(action.slice(7),{autoplay:true});
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
function immersive(hide){document.body.classList.toggle('immersive',hide);$('showUI').hidden=!hide;if(hide){closeTime();$('settings').hidden=true;$('settingsButton').setAttribute('aria-expanded','false');}}
$('hideUI').addEventListener('click',()=>immersive(true));$('showUI').addEventListener('click',()=>immersive(false));
window.addEventListener('refuge-social-focus',()=>{keys.clear();keyboardMotion.reset();});
window.addEventListener('keydown',event=>{
  if(document.getElementById('socialDialog')?.open)return;
  if(/INPUT|SELECT|TEXTAREA/.test(event.target.tagName))return;
  const key=event.key.toLowerCase();
  if(cameraLocked()&&[' ','x','w','a','s','d','q','e','arrowup','arrowdown','arrowleft','arrowright','shift'].includes(key)){event.preventDefault();return;}
  if(key==='h'){immersive(!document.body.classList.contains('immersive'));return;}
  if(key==='escape'){immersive(false);closeTime();$('settings').hidden=true;$('settingsButton').setAttribute('aria-expanded','false');$('lecturePanel').hidden=true;$('lectureButton').setAttribute('aria-expanded','false');reader?.close();return;}
  if(event.target.closest('#chalkReader,#lecturePanel,#settings'))return;
  if([' ','x','w','a','s','d','q','e','arrowup','arrowdown','arrowleft','arrowright','shift'].includes(key)){
    event.preventDefault();stopTour();keys.add(key);
  }
});
window.addEventListener('keyup',event=>keys.delete(event.key.toLowerCase()));window.addEventListener('blur',()=>{keys.clear();keyboardMotion.reset();});
document.addEventListener('visibilitychange',()=>{if(document.hidden){keys.clear();keyboardMotion.reset();}});
let resizeTimer;window.addEventListener('resize',()=>{clearTimeout(resizeTimer);resizeTimer=setTimeout(resize,180);});
reduced.addEventListener('change',()=>{if(reduced.matches){touring=false;if(lecture){lecture.playing=false;lecture.staticPage();}updateLabels();}});


$('boardStorage').addEventListener('click',()=>{if(!lecture?.retractable)return;lecture.toggleStorage();boardFollow.touch();stopTour();updateLectureUI();});
let lectureStatus='';
function updateLectureUI(){
  $('boardStorage').hidden=!lecture.retractable;controlLabel($('boardStorage'),lecture.stored?'升起黑板':'收起黑板');$('boardStorage').setAttribute('aria-pressed',String(lecture.stored));
  const voice=lecture.voiceState,voiceUI=reportVoicePresentation(voice);updateVoicePreferences();
  const status=reportProgress||reportLoadError||(voiceUI.message?voiceUI.message+' · '+lecture.status():lecture.status());if(status!==lectureStatus){$('lectureStatus').textContent=status;lectureStatus=status;}
  $('readerOpen').disabled=!lecture.hasSelection;$('lecturePlay').disabled=!lecture.hasSelection||voiceUI.busy||lecture.clock.ended;$('lectureNext').disabled=!lecture.hasSelection||lecture.clock.page===lecture.clock.stopAt;$('lecturePrevious').disabled=!lecture.hasSelection||lecture.clock.page===lecture.clock.startAt;
  for(const id of ['lectureProgress','lecturePage','lectureRewrite'])$(id).disabled=!lecture.hasSelection;
  controlLabel($('lecturePlay'),lecture.clock.ended?'报告已结束':voiceUI.buttonLabel||(lecture.playing?'暂停板书':'继续板书'));$('lecturePlay').setAttribute('aria-pressed',String(lecture.playing));
  $('world').dataset.voicePhase=voice.phase;$('world').dataset.voiceTime=voice.time.toFixed(1);$('world').dataset.voiceDuration=voice.duration.toFixed(1);const highlight=lecture.highlightState;$('world').dataset.voiceHighlight=highlight?highlight.page+':'+highlight.row+':'+highlight.side:'';const cue=lecture.narrationCue;$('world').dataset.voiceRow=String(cue?.row??-1);
  $('lectureProgressValue').textContent=lecture.hasSelection?`${lecture.progress.page+1} / ${lecture.progress.total}`:'—';
  if(document.activeElement!==$('lectureProgress'))$('lectureProgress').value=String(lecture.progress.page+1);
  if(document.activeElement!==$('lecturePage'))$('lecturePage').value=String(lecture.clock.page);
  lecture.heights().forEach((value,i)=>{const slider=$('boardLift'+i);if(document.activeElement!==slider)slider.value=String(value);});
}
function focusLecture(){
  if(!lecture||!cameraIntent.canActivate())return;
  selectShot(0);
}
$('lectureButton').addEventListener('click',()=>{
  if(!lecture)return;reader?.close();$('lecturePanel').hidden=!$('lecturePanel').hidden;$('lectureButton').setAttribute('aria-expanded',String(!$('lecturePanel').hidden));if(!$('lecturePanel').hidden){setSeminarPanel(false);focusLecture();}
});
$('lectureClose').addEventListener('click',()=>{$('lecturePanel').hidden=true;$('lectureButton').setAttribute('aria-expanded','false');});
$('lectureFocus').addEventListener('click',focusLecture);
let teachingShade=false;
$('lectureShade').addEventListener('click',()=>{
  if(!retreat)return;teachingShade=!teachingShade;if(activeRoom===0)retreat.campus.setTeachingShade(teachingShade);else retreat.campus.discussion.blinds[activeRoom-1].visible=teachingShade;
  $('lectureShade').setAttribute('aria-pressed',String(teachingShade));controlLabel($('lectureShade'),teachingShade?'收起遮光帘':'放下海景遮光帘');renderer.shadowMap.needsUpdate=true;
});
$('lecturePlay').addEventListener('click',()=>{if(!lecture)return;lecture.playing=!lecture.playing;if(reduced.matches)lecture.staticPage();});
for(const [id,delta] of [['lecturePrevious',-1],['lectureNext',1]])$(id).addEventListener('click',()=>{if(!lecture)return;seekLecture(lecture.clock.page+delta);});
$('lectureRewrite').addEventListener('click',()=>{if(!lecture)return;lecture.rewrite();if(reduced.matches)lecture.staticPage();else lecture.playing=true;});
$('lecturePage').addEventListener('change',event=>{if(!lecture)return;seekLecture(Number(event.target.value));});
for(let pair=0;pair<3;pair++){
  $('boardLift'+pair).addEventListener('input',event=>{if(!lecture)return;lecture.playing=false;lecture.lift(pair,event.target.value);});
  $('boardSwap'+pair).addEventListener('click',()=>{if(!lecture)return;lecture.playing=false;lecture.lift(pair,1-lecture.heights()[pair]);});
}

async function seekLecture(page){
  const targetLecture=lecture;
  if(!targetLecture.hasSelection)return;
  try{if(await targetLecture.seek(page)&&targetLecture===lecture){
    updateLectureUI();reader?.update();roomLecterns[activeRoom]?.update({playing:lecture.playing,...lecture.progress});
    // Manual seeking never launches a camera or board animation.
    if(SHOTS[shot].lecture&&!speakerView&&!choosingReport&&boardFollow.following&&lecture.followEnabled){blend=null;applyShot(0);motionVelocity.set(0,0,0);motionAcceleration.set(0,0,0);motionSample=false;}
  }}catch(error){$('lectureStatus').textContent=error.message;}
}
$('lectureProgress').addEventListener('input',event=>seekLecture(lecture.clock.startAt+Number(event.target.value)-1));
$('lecternButton').addEventListener('click',()=>{if(lecture&&physicalRoom===activeRoom&&!(activeRoom===0&&retreat.campus.lecternLift?.lowered))enterSpeakerView();});
function activateRoom(index,moveCamera=true){
  if(!rooms[index])return;
  reportRequest++;changingReport=false;reportProgress='';reportLoadError='';
  activeRoom=index;lecture=rooms[index];lecture.setWritingSpeed($('writingSpeed').value);
  $('world').dataset.room=String(index);$('reportSelect').setAttribute('aria-busy','false');
  reader?.close();populateReport();if(moveCamera)selectShot(0,!lecture.hasSelection&&!lecture.disabled);updateSeminarNavigation();
  teachingShade=index===0?retreat.campus.blind.visible:retreat.campus.discussion.blinds[index-1].visible;
  $('lectureShade').setAttribute('aria-pressed',String(teachingShade));
}
function buildSeminarNavigation(){
 const nav=rooms[1].navigation,container=$('seminarChapters');container.replaceChildren();
 for(const chapter of nav.chapters){
  const group=document.createElement('details'),summary=document.createElement('summary');summary.textContent=`${chapter.id} · ${chapter.title}`;group.append(summary);group.open=chapter.id===1;
  for(const part of nav.sections.filter(p=>p.chapter===chapter.id)){
   const button=document.createElement('button');button.textContent='§ '+part.id+' '+part.title;button.dataset.section=part.id;button.title='前置：'+part.prerequisites+'\n目标：'+part.goal;
   button.addEventListener('click',()=>{selectSeminarPart(part);$('seminarGoal').textContent='前置：'+part.prerequisites+'。目标：'+part.goal;});group.append(button);
  }container.append(group);
 }
 $('seminarErratum').addEventListener('click',()=>selectSeminarPart(nav.sections.find(s=>s.id==='5.2'),nav.erratum.start));
 updateSeminarNavigation();
}
async function selectSeminarPart(part,page=part?.start){
 if(!part)return;
 if(activeRoom!==1)activateRoom(1);
 const target=lecture;target.playing=false;
 try{
  if(!await target.setRange(part.start,part.end))return;
  if(page!==part.start)await target.seek(page);
  if(target!==lecture)return;
  target.playing=!reduced.matches;selectShot(0);populateReport();updateLectureUI();reader?.update();updateSeminarNavigation();
  $('seminarGoal').textContent='本次：§ '+part.id+' · '+part.title+'。前置：'+part.prerequisites+'。目标：'+part.goal;
 }catch(error){$('lectureStatus').textContent=error.message;}
}

function updateSeminarNavigation(){
 document.querySelectorAll('#buildingRooms button').forEach(button=>button.setAttribute('aria-pressed',String(button.dataset.lecternLift!==undefined?Boolean(retreat?.campus.lecternLift?.lowered):button.dataset.room!==undefined?Number(button.dataset.room)===activeRoom&&SHOTS[shot].lecture:button.dataset.roomShot===SHOTS[shot].name)));
 $('seminarCurriculum').hidden=Boolean(panelBuilding.walk)||activeRoom!==1;
}
let hallSunRamp=null;
function viewHallSun(event){
 if(cameraLocked())return;
 if(event==='sunrise')retreat.fleet.resetSunrisePass();
 sunriseIntro.cancel();timePresentation.seek();const hour=hallSunStart(event,sceneTime.date,$('sunSize').value==='physical');sceneTime.previewAt(hour);sceneTime.play(1);hallSunRamp=0;$('timeRate').value='30';updateSceneTime();
 const index=SHOTS.findIndex(s=>s.name==='报告厅'+(event==='sunrise'?'看日出':'看日落')),direction=geographicDirectionToCampus(solarState(hour,sceneTime.date).direction),p=SHOTS[index].positions[0];
 for(const target of curves[index].target.points)target.set(p[0]+direction[0]*500,p[1]+(direction[1]-.10)*500,p[2]+direction[2]*500);curves[index].target.updateArcLengths();
 selectShot(index);setSeminarPanel(true,BUILDINGS[0]);
}
function setSeminarPanel(open,building=panelBuilding){
 $('seminarPanel').hidden=!open;
 if(building)panelBuilding=building;
 document.querySelectorAll('#chapters button[data-building]').forEach(b=>b.setAttribute('aria-expanded',String(open&&Number(b.dataset.building)===panelBuilding.number)));
 walkButton.setAttribute('aria-expanded',String(open&&Boolean(panelBuilding.walk)));
 if(!open)return;
 $('seminarPanel').dataset.actionCount=String(panelBuilding.rooms.length);
 $('buildingHeading').textContent=panelBuilding.walk?'漫步':panelBuilding.number+' · '+panelBuilding.name;
 $('buildingRooms').replaceChildren(...panelBuilding.rooms.map(room=>{
   const button=document.createElement('button');renderRoomAction(button,room,{lowered:retreat?.campus.lecternLift?.lowered,walk:panelBuilding.walk});
   if(room.lecternLift)button.dataset.lecternLift='';
   if(room.sunEvent)button.dataset.roomShot='报告厅'+(room.sunEvent==='sunrise'?'看日出':'看日落');
   if(room.room!==undefined)button.dataset.room=String(room.room);
   if(room.shot)button.dataset.roomShot=room.shot;
   button.addEventListener('click',()=>{
     if(room.sunEvent){viewHallSun(room.sunEvent);return;}
     if(room.lecternLift){if(speakerView)selectShot(SHOTS.findIndex(s=>s.name==='报告厅'));retreat.campus.lecternLift.toggle();renderRoomAction(button,room,{lowered:retreat.campus.lecternLift.lowered});button.setAttribute('aria-pressed',String(retreat.campus.lecternLift.lowered));return;}
     if(room.room!==undefined)activateRoom(room.room,!room.shot);
     if(room.shot)selectShot(SHOTS.findIndex(s=>s.name===room.shot));
     updateSeminarNavigation();
   });return button;
 }));updateSeminarNavigation();
}
$('seminarClose').addEventListener('click',()=>setSeminarPanel(false));

function syncRoomControls(){
 const room=teachingRoomAt(camera.position);
 rooms.forEach((target,index)=>target.setPresence(room===index));
 if(room!==physicalRoom){
   physicalRoom=room;$('world').dataset.physicalRoom=String(room);
   if(room<0){$('lecturePanel').hidden=true;$('lectureButton').setAttribute('aria-expanded','false');reader?.close();}
 }
 // During a journey the selected destination owns the camera; bind controls on arrival.
 if(room>=0&&room!==activeRoom&&!blend){activateRoom(room,false);speakerView=false;choosingReport=false;}
 reader?.chapter(room>=0&&room===activeRoom&&!speakerView&&Boolean(SHOTS[shot].lecture),$('lecturePanel').hidden);
 $('roomControls').hidden=room<0||room!==activeRoom||lecture.disabled;
 if(room>=0&&lecture.disabled)$('mode').textContent='本层板书暂未开放';
 $('roomControls').setAttribute('aria-label',room===0?'报告厅板书':room>0?'教学楼 '+room+' 层板书':'房间外');
}

$('surfSound').addEventListener('change',async event=>{try{await surfAudio.setEnabled(event.target.value==='on');}catch(error){event.target.value='off';console.error(error);}});

for(const [id,key,parse] of [['coastGrid','grid',v=>v==='on'],['coastTide','tide',Number],['coastTidal','tidal',v=>v==='on'],['coastPause','paused',v=>v==='on']]){
 $(id).addEventListener('input',event=>{if(retreat)retreat.ocean.userData.study.settings[key]=parse(event.target.value);});
}

// Capture only the scene canvas synchronously after rendering; no chat/account UI.
window.refugeCaptureFrame=()=>{
 if(!renderer||!retreat)throw Error('场景尚未准备好');
 if(profile.direct)renderer.render(scene,camera);else composer.render();
 const source=renderer.domElement,scale=Math.min(1,1280/Math.max(source.width,source.height)),copy=document.createElement('canvas');copy.width=Math.max(1,Math.round(source.width*scale));copy.height=Math.max(1,Math.round(source.height*scale));copy.getContext('2d').drawImage(source,0,0,copy.width,copy.height);
 let image=copy.toDataURL('image/jpeg',.82);for(const quality of [.7,.55,.4]){if(image.length<=560000)break;image=copy.toDataURL('image/jpeg',quality);}if(image.length>560000){const smaller=document.createElement('canvas');smaller.width=Math.round(copy.width*.7);smaller.height=Math.round(copy.height*.7);smaller.getContext('2d').drawImage(copy,0,0,smaller.width,smaller.height);image=smaller.toDataURL('image/jpeg',.55);}if(image.length>560000)throw Error('截图压缩失败，请重试');return image;
};

let photoBusy=false;
$('photoButton').addEventListener('click',async()=>{
 if(photoBusy||!entered||!renderer||!retreat)return;
 photoBusy=true;$('photoButton').disabled=true;$('photoStatus').hidden=false;$('photoStatus').textContent='正在拍摄…';
 try{const blob=await capturePhoto(renderer,scene,camera);downloadPhoto(blob);$('photoStatus').textContent='照片已生成';}
 catch(error){console.error('[Photo]',error);$('photoStatus').textContent='拍摄失败，请重试';}
 finally{photoBusy=false;$('photoButton').disabled=false;setTimeout(()=>{$('photoStatus').hidden=true;},3500);}
});
