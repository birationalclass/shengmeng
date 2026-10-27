import {prepareBlackboardEntry} from './blackboard-startup.js';
import {downloadCoursePacks} from './course-pack-cache.js';
import {resourceFetch} from './resource-fetch.js';
import {startReadyCourse} from './course-ready.js';
import * as T from 'three';
import {OrbitControls} from '../3d/vendor/OrbitControls.js';
import {createLecture} from './lecture.js';
import {configureLectureRoot} from './site-layout.js';
import {loadMathRuntime,loadBoardFonts} from './staged-startup.js';
import {batchLectureGeometry} from './blackboard-lecture-batching.js';
import {isClassroomBreak,classroomBreakTime} from './blackboard-break.js';
import {createBlackboardHall,SMART_SCREEN_BACKGROUND} from './blackboard-hall.js';
import {constrainHallCamera,hallOverview,HALL_CAMERA_BOUNDS} from './blackboard-camera.js';
import {configureCameraInput} from './camera-input.js';
import {BoardFollow} from './board-follow.js';
import {BoardCameraMotion} from './board-camera-motion.js';
import {bindPhysicalButtons,physicalHitAction} from './physical-buttons.js';
import {createCourseLibrary} from './course-library.js';
import {CLASSROOM_PROGRAMS} from './classroom-catalog.js?v=course-packs-20261026';
import {loadErasingSpeed,saveErasingSpeed} from './board-erasing-speed.js';
import {BlackboardFrameBudget,blackboardPixelRatio} from './blackboard-performance.js';
import {startDeferredTextures} from './deferred-textures.js';

const $=id=>document.getElementById(id),canvas=$('world'),scene=new T.Scene();scene.background=new T.Color('#b5b5b2');
const renderer=new T.WebGLRenderer({canvas,antialias:true,alpha:false,powerPreference:'high-performance'});
renderer.setPixelRatio(blackboardPixelRatio(devicePixelRatio,innerWidth,innerHeight));renderer.outputColorSpace=T.SRGBColorSpace;renderer.toneMapping=T.ACESFilmicToneMapping;renderer.toneMappingExposure=1.12;
const camera=new T.PerspectiveCamera(65,innerWidth/innerHeight,.06,75),controls=new OrbitControls(camera,canvas);
controls.maxDistance=35;controls.minDistance=.25;controls.maxPolarAngle=Math.PI*.96;controls.minPolarAngle=.04;
configureCameraInput(controls,canvas);
const follow=new BoardFollow(),motion=new BoardCameraMotion(),keys=new Set(),hall=createBlackboardHall(scene);
const lectureRoot=new T.Group();configureLectureRoot(lectureRoot);scene.add(lectureRoot);
const frames=new BlackboardFrameBudget(),diagnosticStart=performance.now();let cpuMs=0,raf=0,timer=0,inputUntil=0,lastUIKey='',overviewUntil=0,quality='auto',targetFPS=60,breakView=null,breakControlsEnabled=true,resizePending=true,lectureBatching=null;
let startupPreparing=true;controls.enabled=false;
let lecture=null,view='overview',library=null,selecting=false,last=performance.now(),lastUI=0,lastPageKey='',lastDiagnostic=0;
const reduced=matchMedia('(prefers-reduced-motion: reduce)').matches;
$('erasingSpeed').value=String(loadErasingSpeed());
function applyErasingSpeed(){const value=Number($('erasingSpeed').value);lecture?.setErasingSpeed(value);saveErasingSpeed(value);$('erasingSpeedValue').textContent=value+'×';wake();}
$('erasingSpeedValue').textContent=$('erasingSpeed').value+'×';$('erasingSpeed').addEventListener('input',applyErasingSpeed);
function apply(pose){camera.position.fromArray(pose.position);controls.target.fromArray(pose.target);camera.fov=pose.fov;camera.updateProjectionMatrix();camera.lookAt(controls.target);}
function pose(){return{position:camera.position.toArray(),target:controls.target.toArray(),fov:camera.fov};}
function focus(){overviewUntil=0;view='board';if(lecture)lecture.autoCamera=true;follow.reset();setResolution();wake();}
function overview(){view='overview';overviewUntil=lecture?.hasSelection&&lecture.autoCamera?performance.now()+5000:0;follow.reset();setResolution();wake();}
apply(hallOverview(camera.aspect));constrainHallCamera(camera,controls.target);
controls.addEventListener('start',()=>{follow.begin();if(lecture&&!lecture.autoCamera){view='manual';overviewUntil=0;}motion.reset();inputUntil=performance.now()+750;wake();});controls.addEventListener('end',()=>{follow.end();inputUntil=performance.now()+750;wake();});controls.addEventListener('change',()=>frames.invalidate());
const editable=target=>Boolean(target.closest?.('input,select,textarea,button,dialog'));
addEventListener('keydown',e=>{if(startupPreparing||editable(e.target))return;const key=e.key.toLowerCase();if(breakView)return;if(key===' '){if(!e.repeat&&!e.ctrlKey&&!e.metaKey&&!e.altKey&&lecture?.hasSelection&&!selecting&&lecture.courseLoadState.phase==='ready'){e.preventDefault();void action('voice:toggle');}return;}if(['w','a','s','d','q','e','z','x','arrowup','arrowdown','arrowleft','arrowright'].includes(key)){keys.add(key);follow.begin();if(lecture&&!lecture.autoCamera){view='manual';overviewUntil=0;}wake();e.preventDefault();}});
addEventListener('keyup',e=>{keys.delete(e.key.toLowerCase());if(!keys.size)follow.end();wake();});
addEventListener('blur',()=>{keys.clear();follow.end();});
document.addEventListener('visibilitychange',()=>{keys.clear();follow.end();lecture?.setPresence(!document.hidden);last=performance.now();if(document.hidden){cancelAnimationFrame(raf);clearTimeout(timer);raf=timer=0;}else wake();});
function keyboard(dt){
 if(!keys.size)return;
 const forward=controls.target.clone().sub(camera.position);forward.y=0;forward.normalize();const right=new T.Vector3().crossVectors(forward,new T.Vector3(0,1,0));
 const has=(...v)=>v.some(k=>keys.has(k))?1:0,delta=forward.multiplyScalar(has('w','arrowup')-has('s','arrowdown')).addScaledVector(right,has('e','arrowright')-has('q','arrowleft'));delta.y=has('z')-has('x');if(delta.lengthSq())delta.normalize().multiplyScalar(dt*2.5);camera.position.add(delta);controls.target.add(delta);
 const yaw=(has('a')-has('d'))*dt*.8;if(yaw){const direction=controls.target.clone().sub(camera.position).applyAxisAngle(new T.Vector3(0,1,0),yaw);controls.target.copy(camera.position).add(direction);}
}
function setResolution(focused=view==='board'){const ratio=quality==='saver'?1:quality==='clear'?Math.max(1,Math.min(devicePixelRatio||1,2,Math.sqrt(4000000/(innerWidth*innerHeight)))):blackboardPixelRatio(devicePixelRatio,innerWidth,innerHeight,focused);if(renderer.getPixelRatio()!==ratio)renderer.setPixelRatio(ratio);}
function resize(){resizePending=true;setResolution();renderer.setSize(innerWidth,innerHeight,false);camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();motion.reset();wake();}addEventListener('resize',resize);resize();
function pageOptions(){const key=lecture.report.id+':'+lecture.clock.startAt+':'+lecture.clock.stopAt;if(key===lastPageKey)return;lastPageKey=key;$('page').replaceChildren();for(let i=lecture.clock.startAt;i<=lecture.clock.stopAt;i++){const o=document.createElement('option');o.value=i;o.textContent=(i+1)+' · '+(lecture.copy(i).title||lecture.pages[i].title);$('page').append(o);}}
function updateUI(){if(!lecture)return;const selected=lecture.hasSelection,blocked=selecting||['loading','error'].includes(lecture.courseLoadState.phase),key=[selected,blocked,lecture.report.id,lecture.navigationPage,lecture.playing,lecture.language,lecture.status(),lecture.courseLoadState.phase,Math.floor((lecture.courseLoadState.ratio||0)*100),lecture.autoCamera,view,Math.ceil(follow.remaining)].join('|');if(key===lastUIKey)return;lastUIKey=key;$('catalog').disabled=selecting;for(const id of ['play','previous','next','page','language','rate','closer','farther','focus'])$(id).disabled=!selected||blocked;if(selected){pageOptions();$('page').value=lecture.navigationPage;}$('previous').disabled=!selected||blocked||lecture.navigationPage<=lecture.clock.startAt;$('next').disabled=!selected||blocked||lecture.navigationPage>=lecture.clock.stopAt;$('play').innerHTML='<svg viewBox="0 0 24 24" aria-hidden="true" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"><path d="'+(lecture.playing?'M8 5v14M16 5v14':'m8 4 12 8-12 8Z')+'"/></svg>';$('play').title=lecture.playing?'暂停':'播放';$('play').setAttribute('aria-label',lecture.playing?'暂停板书':'播放板书');$('language').textContent=lecture.language==='zh'?'中文 → EN':'EN → 中文';$('autoFollow').checked=lecture.autoCamera;$('autoState').textContent=!lecture.autoCamera?'已关闭 · 自由观察':!lecture.hasSelection?'选课后自动跟随':view==='overview'?'全景预览 · 5秒后回到当前板':follow.remaining>0?'手动观察 · '+Math.ceil(follow.remaining)+'秒后回位':'已开启 · 跟随当前黑板';$('status').textContent=lecture.courseLoadState.phase==='error'?lecture.courseLoadState.error:selecting?'准备开场 '+Math.floor((lecture.courseLoadState.ratio||0)*100)+'%':selected?lecture.status():'选择课堂，开始板书';$('notice').hidden=!lecture.voiceState.error;if(lecture.voiceState.error)$('notice').textContent=lecture.voiceState.error;$('topic').textContent=selected?lecture.report.topic||lecture.report.label||lecture.report.title||'报告厅':'报告厅';}
async function selectReport(id,{autoplay=true,initial=false}={}){if(selecting)return false;selecting=true;updateUI();wake();try{
 const ready=await startReadyCourse(lecture,id,{autoplay:autoplay&&!initial,firstBoardOnly:true,onSelected:()=>{if(!initial){if(lecture.autoCamera)focus();else wake();}},onProgress:state=>{canvas.dataset.courseLoading=JSON.stringify(state);$('status').textContent='准备开场 '+Math.floor(state.ratio*100)+'%';if(initial)$('loadingText').textContent='准备首板内容与语音 · '+Math.floor(state.ratio*100)+'%';wake();}});
 if(initial){
  if(!ready)throw Error('课程未准备好');setResolution(true);
  canvas.dataset.startupPreparation=JSON.stringify(await prepareBlackboardEntry({lecture,renderer,scene,camera,target:controls.target,prepareTextures:()=>startDeferredTextures(()=>{},{phase:'hall'}),onStage:(stage,label)=>{canvas.dataset.startupPhase=stage;$('loadingText').textContent=label;}}));
  startupPreparing=false;controls.enabled=true;motion.reset();last=performance.now();$('loading').hidden=true;
  if(lecture.autoCamera)focus();else wake();await new Promise(resolve=>requestAnimationFrame(resolve));if(autoplay)await lecture.toggleVoice();
 }else if(lecture.autoCamera)focus();else wake();return ready;
 }catch(error){$('status').textContent=error.message;canvas.dataset.courseLoading=JSON.stringify(lecture.courseLoadState);if(initial)throw error;return false;}
 finally{selecting=false;lastPageKey='';updateUI();wake();}}

function openLibrary(){library.open('classroom');}
async function action(a){
 if(startupPreparing||!lecture||selecting||breakView||['loading','error'].includes(lecture.courseLoadState.phase))return;
 try{
  if(a==='voice:toggle'||a==='lectern:play')await lecture.toggleVoice();
  else if(a==='board:previous'||a==='lectern:previous'){await lecture.step(-1);focus();}
  else if(a==='board:next'||a==='lectern:next'){await lecture.step(1);focus();}
  else if(a.startsWith('page:seek:')){await lecture.seek(Number(a.slice(10)),{preservePlayback:true});focus();}
  else if(a==='camera:closer'||a==='camera:farther'){lecture.adjustCameraZoom(a==='camera:farther'?1:-1);focus();}
  else if(a==='camera:toggle')setAutoFollow(!lecture.autoCamera);
  else if(a==='language')await lecture.setLanguage(lecture.language==='zh'?'en':'zh');
  else if(a==='board:lottery')await lecture.drawStudent();
  else if(a==='board:roster')await lecture.importStudentRoster();
  else if(a==='board:time')lecture.toggleTimeDisplay();
  else if(a==='board:reveal')await lecture.revealCurrent();
  else if(a==='activity:skip')await lecture.skipClassroomActivity();
  else if(a==='lectern:stow')return;
  else if(a==='lectern:view'){const p=hall.lectern.speakerPose(camera.aspect);apply({position:p.position.toArray(),target:p.target.toArray(),fov:p.fov});follow.touch();}
  else if(a==='course:catalog')openLibrary();
  else if(a.startsWith('course:external:'))window.open('https://birationalclass.github.io/shengmeng/courses/abstract-algebra/2026-fall/?view=lesson&section='+a.slice(16),'_blank','noopener');
  else if(a.startsWith('course:section:'))await selectReport(a.slice(15));
  else if(a==='course:manuscript')window.open(lecture.report.url,'_blank','noopener');
  else if(a.startsWith('seminar:section:')){const part=lecture.navigation?.sections?.find(s=>s.id===a.split(':')[2]);if(part){await lecture.setRange(part.start,part.end);focus();}}
  else if(a.startsWith('course:section:'))await selectReport(a.slice(15));
  else if(a.startsWith('screen:')||a.startsWith('program:')||a.startsWith('course:')||a.startsWith('seminar:'))lecture.screenAction(a);
  updateUI();wake();
 }catch(error){$('status').textContent=error.message;}
}
$('catalog').onclick=()=>openLibrary();$('overview').onclick=overview;$('focus').onclick=focus;
$('play').onclick=()=>action('voice:toggle');$('previous').onclick=()=>action('board:previous');$('next').onclick=()=>action('board:next');$('closer').onclick=()=>action('camera:closer');$('farther').onclick=()=>action('camera:farther');$('language').onclick=()=>action('language');
$('page').onchange=()=>action('page:seek:'+$('page').value);$('rate').onchange=()=>{lecture?.setVoiceRate(Number($('rate').value));wake();};
function showSettings(open){$('settings').hidden=!open;$('settingsButton').setAttribute('aria-expanded',String(open));}
function immersive(hidden){document.body.classList.toggle('immersive',hidden);$('showUI').hidden=!hidden;if(hidden)showSettings(false);}
$('settingsButton').onclick=()=>showSettings($('settings').hidden);$('settingsClose').onclick=()=>showSettings(false);
$('hideUI').onclick=()=>immersive(true);$('showUI').onclick=()=>immersive(false);
function setAutoFollow(enabled){if(!lecture)return;lecture.autoCamera=Boolean(enabled);if(enabled)focus();else{view='manual';overviewUntil=0;follow.touch();}updateUI();wake();}
$('autoFollow').onchange=()=>setAutoFollow($('autoFollow').checked);
$('quality').onchange=()=>{quality=$('quality').value;setResolution();wake();};$('frameRate').onchange=()=>{targetFPS=Number($('frameRate').value);frames.maxFPS=targetFPS;wake();};
function fullscreenFallback(enabled){document.body.classList.toggle('fullscreen-fallback',enabled);$('exitFullscreen').hidden=!enabled;$('fullscreen').setAttribute('aria-pressed',String(enabled));resize();}
$('exitFullscreen').onclick=()=>fullscreenFallback(false);
$('fullscreen').onclick=async()=>{if(document.body.classList.contains('fullscreen-fallback')){fullscreenFallback(false);return;}try{if(document.fullscreenElement||document.webkitFullscreenElement){const exit=document.exitFullscreen||document.webkitExitFullscreen;if(exit)await exit.call(document);}else{const enter=document.documentElement.requestFullscreen||document.documentElement.webkitRequestFullscreen;if(enter)await enter.call(document.documentElement);else fullscreenFallback(true);}}catch{fullscreenFallback(true);}};
document.addEventListener('fullscreenchange',()=>{$('fullscreen').setAttribute('aria-pressed',String(Boolean(document.fullscreenElement)));resize();});
document.addEventListener('pointerdown',e=>{if(!$('settings').hidden&&!e.target.closest('#settings,#settingsButton'))showSettings(false);});
addEventListener('keydown',e=>{if(e.key==='Escape'){showSettings(false);if(document.body.classList.contains('fullscreen-fallback'))fullscreenFallback(false);}if(editable(e.target))return;if(e.key.toLowerCase()==='h'){immersive(!document.body.classList.contains('immersive'));e.preventDefault();}if(e.key==='Escape'){showSettings(false);if(document.body.classList.contains('fullscreen-fallback'))fullscreenFallback(false);}});
function activity(){const state=lecture?.screenMode;return{hidden:document.hidden,moving:Boolean(keys.size||follow.interacting||performance.now()<inputUntil||motion.segment&&motion.segment.elapsed<motion.segment.duration),playing:Boolean(lecture?.playing),phase:lecture?.clock.phase||'',busy:selecting||Boolean(lecture&&lecture.storageProgress>0&&lecture.storageProgress<1)||Boolean(state&&Math.abs(state.reportAlpha-(state.power&&state.mode==='report'?1:0))>.005)};}
function wake(){frames.invalidate();clearTimeout(timer);timer=0;if(!document.hidden&&!raf)raf=requestAnimationFrame(animate);}
function next(){if(document.hidden)return;const fps=frames.cadence(activity());if(fps>=15){if(!raf)raf=requestAnimationFrame(animate);}else timer=setTimeout(()=>{timer=0;if(!raf)raf=requestAnimationFrame(animate);},480);}
function visualSignature(){const c=lecture?.clock,v=lecture?.voiceState,tool=lecture?.toolState,screen=lecture?.screenMode,highlight=lecture?.highlightState;const numbers=[...camera.position.toArray(),...controls.target.toArray(),camera.fov,lecture?.storageProgress||0,c?.progress||0,...(c?.slots.flatMap(s=>[s.page,s.progress])||[]),tool?.pickup??-1,tool?.returning??-1,screen?.reportAlpha||0,screen?.brightness||0,highlight?.alpha||0];return numbers.map(n=>Math.round(n*100000)).join(',')+'|'+[c?.page,c?.phase,lecture?.report.id,lecture?.hasSelection,lecture?.stored,lecture?.seeking,lecture?.preloadState.prepared,lecture?.courseLoadState.ratio,lecture?.courseLoadState.phase,Math.floor(v?.time||0),screen?.mode,screen?.power,lecture?.timeDisplayMode==='local'&&!lecture.stored?Math.floor(Date.now()/1000):0].join(':');}
function animate(stamp){raf=0;if(document.hidden)return;if(overviewUntil&&stamp>=overviewUntil&&!follow.interacting){overviewUntil=0;view='board';follow.reset();frames.invalidate();}const state=activity();if(!frames.updateDue(stamp,state)){next();return;}const workStart=performance.now(),dt=Math.max(0,Math.min(.1,(stamp-last)/1000));last=stamp;
 lecture?.update(dt,reduced);
 const resting=isClassroomBreak(lecture?.pages[lecture.clock.page]);
 if(resting){if(!breakView){breakView=pose();breakControlsEnabled=controls.enabled;controls.enabled=false;keys.clear();motion.reset();overviewUntil=0;inputUntil=0;showSettings(false);document.body.classList.add('on-break');}const board=lecture.voiceManifest?.boards.find(b=>b.page===lecture.clock.page),count=classroomBreakTime(lecture.pages[lecture.clock.page],board,lecture.voiceState);$('breakCountdown').hidden=false;if($('breakTime').textContent!==count.text)$('breakTime').textContent=count.text;apply(breakView);}
 else if(breakView){controls.enabled=breakControlsEnabled;breakView=null;$('breakCountdown').hidden=true;document.body.classList.remove('on-break');motion.reset();if(lecture.autoCamera){view='board';follow.reset();}frames.invalidate();}
 const tracking=!startupPreparing&&!resting&&follow.following&&(view==='overview'||lecture?.followEnabled);
 if(tracking){const desired=view==='board'?lecture.cameraView(camera.aspect,57):hallOverview(camera.aspect);apply(motion.sample(pose(),{position:desired.position.toArray?.()||desired.position,target:desired.target.toArray?.()||desired.target,fov:desired.fov},dt,{immediate:reduced}));if(view==='overview'&&lecture&&!lecture.autoCamera&&motion.segment?.elapsed>=motion.segment?.duration)view='manual';}else if(!resting){keyboard(dt);controls.update();}
 constrainHallCamera(camera,controls.target);
 hall.lectern.update({playing:lecture?.playing,page:lecture?.navigationPage??0,total:lecture?.progress.total??0,seeking:lecture?.seeking,retractable:lecture?.retractable??false,stored:lecture?.stored??false,storageProgress:lecture?.storageProgress??1});
 if(stamp-lastUI>200){lastUI=stamp;updateUI();}
 if(!startupPreparing&&(!resting||resizePending)&&frames.drawDue(stamp,visualSignature())){scene.updateMatrixWorld();renderer.render(scene,camera);resizePending=false;}else if(resting)frames.dirty=false;
 cpuMs+=performance.now()-workStart;
 if(stamp-lastDiagnostic>500){lastDiagnostic=stamp;canvas.dataset.camera=JSON.stringify({position:camera.position.toArray(),target:controls.target.toArray(),bounds:HALL_CAMERA_BOUNDS});canvas.dataset.breakState=JSON.stringify({active:resting,seconds:resting?classroomBreakTime(lecture.pages[lecture.clock.page],lecture.voiceManifest?.boards.find(b=>b.page===lecture.clock.page),lecture.voiceState).seconds:null});canvas.dataset.follow=JSON.stringify({view,enabled:lecture?.autoCamera,eligible:lecture?.followEnabled,following:follow.following,remaining:follow.remaining,temporaryOverview:Boolean(overviewUntil)});canvas.dataset.preload=JSON.stringify(lecture?.preloadState||{});canvas.dataset.courseLoading=JSON.stringify(lecture?.courseLoadState||{});canvas.dataset.board=String(lecture?.navigationPage??-1);canvas.dataset.voicePhase=lecture?.voiceState.phase||'idle';canvas.dataset.voiceTime=String(lecture?.voiceState.time||0);canvas.dataset.renderStats=JSON.stringify({frames:frames.frames,elapsed:performance.now()-diagnosticStart,calls:renderer.info.render.calls,triangles:renderer.info.render.triangles,pixelRatio:renderer.getPixelRatio(),cpuMs,batching:hall.batching,lectureBatching});}
 next();
}
let resumingAutoplay=false;function resumeAutoplay(){const v=lecture?.voiceState;if(!selecting&&lecture?.courseLoadState.phase==='ready'&&!resumingAutoplay&&v?.phase==='paused'&&v.time<.05&&v.error){resumingAutoplay=true;void lecture.toggleVoice().finally(()=>{resumingAutoplay=false;wake();});}}document.addEventListener('click',resumeAutoplay);document.addEventListener('keydown',resumeAutoplay,{capture:true});
for(const name of ['pointerdown','pointerup','pointermove','wheel'])canvas.addEventListener(name,()=>{inputUntil=performance.now()+200;if(breakView)return;if(overviewUntil&&(name==='wheel'||follow.interacting))overviewUntil=performance.now()+5000;wake();},{passive:true});
scene.matrixAutoUpdate=false;scene.matrixWorldAutoUpdate=false;wake();
async function boot(){try{
 await Promise.all([loadMathRuntime(),loadBoardFonts()]);
 lecture=await createLecture(lectureRoot,renderer,{camera,retractable:false,startStored:false,requireSelection:true,fixedBoards:false,classroomOnly:true,reports:CLASSROOM_PROGRAMS,preloadMode:'background',defaultReport:'sylow-theorems',initialLanguage:'zh',floorMaterial:hall.carpetMaterial,isActive:()=>!document.hidden,onProgress:p=>{$('loadingText').textContent='准备报告厅 · '+Math.round(p*100)+'%';}});
 applyErasingSpeed();
 lectureBatching=batchLectureGeometry(T,lectureRoot);lectureRoot.updateMatrix();lectureRoot.matrixAutoUpdate=false;
 library=createCourseLibrary({getLecture:()=>lecture,onSelect:selectReport,classroomOnly:true});
 const ray=new T.Raycaster(),pointer=new T.Vector2();
 bindPhysicalButtons(canvas,controls,event=>{const rect=canvas.getBoundingClientRect();pointer.set((event.clientX-rect.left)/rect.width*2-1,1-(event.clientY-rect.top)/rect.height*2);scene.updateMatrixWorld(true);ray.setFromCamera(pointer,camera);ray.far=25;const hit=ray.intersectObjects([...lecture.hoverTargets,...hall.lectern.targets].filter(o=>{for(let p=o;p;p=p.parent)if(!p.visible)return false;return true;}),false)[0];if(!hit)return null;hit.object.userData.action=physicalHitAction(hit,lecture.clock);return hit.object;},a=>void action(a));
 canvas.addEventListener('pointermove',()=>lecture.screenWake(),{passive:true});
 canvas.dataset.mode='blackboard';canvas.dataset.smartScreenBackground=SMART_SCREEN_BACKGROUND;canvas.dataset.startupPhase='content';updateUI();wake();
 const course=new URLSearchParams(location.search).get('course')||'sylow-theorems';await selectReport(lecture.reports.some(r=>r.id===course)?course:'sylow-theorems',{initial:true});canvas.dataset.voicePhase=lecture.voiceState.phase;canvas.dataset.voiceTime=String(lecture.voiceState.time);canvas.dataset.ready='true';updateUI();wake();
 }catch(error){$('loadingText').textContent='报告厅准备失败：'+error.message;$('retry').hidden=false;console.error(error);}}
canvas.addEventListener('click',()=>{if(!selecting&&lecture?.courseLoadState.phase==='error')void selectReport(lecture.report.id);});
$('retry').onclick=()=>location.reload();void boot();

$('cacheCourse').addEventListener('click',async()=>{if(!lecture?.report?.resourceIndex)return;const button=$('cacheCourse'),report=lecture.report;button.disabled=true;try{await downloadCoursePacks(report,{fetcher:resourceFetch,onProgress:s=>{button.textContent='保存中 '+s.completed+' / '+s.total;}});button.textContent='本课已保存';}catch{button.textContent='保存失败，点击重试';}finally{button.disabled=false;}});

if(globalThis.REFUGE_LOCAL){$('cacheCourse').hidden=true;$('cacheCourse').nextElementSibling.textContent='离线包已包含全部课程资源。';}
