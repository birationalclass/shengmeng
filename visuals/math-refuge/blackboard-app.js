import * as T from 'three';
import {OrbitControls} from '../3d/vendor/OrbitControls.js';
import {createLecture} from './lecture.js';
import {configureLectureRoot} from './site-layout.js';
import {loadMathRuntime,loadBoardFonts} from './staged-startup.js';
import {createBlackboardHall,SMART_SCREEN_BACKGROUND} from './blackboard-hall.js';
import {constrainHallCamera,hallOverview,HALL_CAMERA_BOUNDS} from './blackboard-camera.js';
import {configureCameraInput} from './camera-input.js';
import {BoardFollow} from './board-follow.js';
import {BoardCameraMotion} from './board-camera-motion.js';
import {bindPhysicalButtons,physicalHitAction} from './physical-buttons.js';
import {createCourseLibrary} from './course-library.js';
import {createScreenWebview} from './screen-webview.js';
import {VIDEO_SITES} from './smart-glass-hub.js';
import {startDeferredTextures} from './deferred-textures.js';

const $=id=>document.getElementById(id),canvas=$('world'),scene=new T.Scene();scene.background=new T.Color('#b5b5b2');
const renderer=new T.WebGLRenderer({canvas,antialias:true,alpha:true,powerPreference:'high-performance'});
renderer.setPixelRatio(Math.min(devicePixelRatio||1,2));renderer.outputColorSpace=T.SRGBColorSpace;renderer.toneMapping=T.ACESFilmicToneMapping;renderer.toneMappingExposure=1.12;
const camera=new T.PerspectiveCamera(65,innerWidth/innerHeight,.06,75),controls=new OrbitControls(camera,canvas);
controls.maxDistance=35;controls.minDistance=.25;controls.maxPolarAngle=Math.PI*.96;controls.minPolarAngle=.04;
configureCameraInput(controls,canvas);
const follow=new BoardFollow(),motion=new BoardCameraMotion(),keys=new Set(),hall=createBlackboardHall(scene);
const webview=createScreenWebview(T),lectureRoot=new T.Group();configureLectureRoot(lectureRoot);scene.add(lectureRoot);
let lecture=null,view='overview',library=null,selecting=false,last=performance.now(),lastUI=0,lastPageKey='',lastDiagnostic=0;
const reduced=matchMedia('(prefers-reduced-motion: reduce)').matches;
function apply(pose){camera.position.fromArray(pose.position);controls.target.fromArray(pose.target);camera.fov=pose.fov;camera.updateProjectionMatrix();camera.lookAt(controls.target);}
function pose(){return{position:camera.position.toArray(),target:controls.target.toArray(),fov:camera.fov};}
function focus(){view='board';if(lecture)lecture.autoCamera=true;follow.reset();motion.reset();}
function overview(){view='overview';follow.reset();motion.reset();}
apply(hallOverview(camera.aspect));constrainHallCamera(camera,controls.target);
controls.addEventListener('start',()=>{follow.begin();motion.reset();});controls.addEventListener('end',()=>follow.end());
const editable=target=>Boolean(target.closest?.('input,select,textarea,button,dialog'));
addEventListener('keydown',e=>{if(editable(e.target))return;const key=e.key.toLowerCase();if(['w','a','s','d','q','e',' ','x','arrowup','arrowdown','arrowleft','arrowright'].includes(key)){keys.add(key);follow.begin();e.preventDefault();}});
addEventListener('keyup',e=>{keys.delete(e.key.toLowerCase());if(!keys.size)follow.end();});
addEventListener('blur',()=>{keys.clear();follow.end();});
document.addEventListener('visibilitychange',()=>{keys.clear();follow.end();lecture?.setPresence(!document.hidden);last=performance.now();});
function keyboard(dt){
 if(!keys.size)return;
 const forward=controls.target.clone().sub(camera.position);forward.y=0;forward.normalize();const right=new T.Vector3().crossVectors(forward,new T.Vector3(0,1,0));
 const has=(...v)=>v.some(k=>keys.has(k))?1:0,delta=forward.multiplyScalar(has('w','arrowup')-has('s','arrowdown')).addScaledVector(right,has('e','arrowright')-has('q','arrowleft'));delta.y=has(' ')-has('x');if(delta.lengthSq())delta.normalize().multiplyScalar(dt*2.5);camera.position.add(delta);controls.target.add(delta);
 const yaw=(has('a')-has('d'))*dt*.8;if(yaw){const direction=controls.target.clone().sub(camera.position).applyAxisAngle(new T.Vector3(0,1,0),yaw);controls.target.copy(camera.position).add(direction);}
}
function resize(){renderer.setSize(innerWidth,innerHeight,false);camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();motion.reset();}addEventListener('resize',resize);resize();
function pageOptions(){const key=lecture.report.id+':'+lecture.clock.startAt+':'+lecture.clock.stopAt;if(key===lastPageKey)return;lastPageKey=key;$('page').replaceChildren();for(let i=lecture.clock.startAt;i<=lecture.clock.stopAt;i++){const o=document.createElement('option');o.value=i;o.textContent=(i+1)+' · '+(lecture.copy(i).title||lecture.pages[i].title);$('page').append(o);}}
function updateUI(){if(!lecture)return;const selected=lecture.hasSelection;for(const id of ['play','previous','next','page','language','rate','closer','farther','focus'])$(id).disabled=!selected||selecting;if(selected){pageOptions();$('page').value=lecture.navigationPage;}$('previous').disabled=!selected||selecting||lecture.navigationPage<=lecture.clock.startAt;$('next').disabled=!selected||selecting||lecture.navigationPage>=lecture.clock.stopAt;$('play').textContent=lecture.playing?'暂停':'播放';$('play').setAttribute('aria-label',lecture.playing?'暂停板书':'播放板书');$('language').textContent=lecture.language==='zh'?'EN':'中';$('status').textContent=selecting?'正在准备板书…':selected?lecture.status():'选择课堂或报告，开始板书';$('topic').textContent=selected?lecture.report.topic||lecture.report.label||lecture.report.title||'报告厅':'报告厅';}
async function selectReport(id,{autoplay=true}={}){if(selecting)return false;selecting=true;updateUI();try{webview.close();await lecture.setReport(id,{autoplay});if(lecture.report.kind==='classroom')await lecture.setLanguage('zh');lecture.setVoiceRate(lecture.report.narration?.defaultPlaybackRate??1);focus();return true;}catch(error){$('status').textContent=error.message;throw error;}finally{selecting=false;lastPageKey='';updateUI();}}
function openLibrary(tab='classroom'){library.open(tab);}
async function action(a){
 if(!lecture||selecting)return;
 try{
  if(a==='voice:toggle'||a==='lectern:play')await lecture.toggleVoice();
  else if(a==='board:previous'||a==='lectern:previous'){await lecture.step(-1);focus();}
  else if(a==='board:next'||a==='lectern:next'){await lecture.step(1);focus();}
  else if(a.startsWith('page:seek:')){await lecture.seek(Number(a.slice(10)),{preservePlayback:true});focus();}
  else if(a==='camera:closer'||a==='camera:farther'){lecture.adjustCameraZoom(a==='camera:farther'?1:-1);focus();}
  else if(a==='camera:toggle'){lecture.autoCamera=!lecture.autoCamera;if(lecture.autoCamera)focus();}
  else if(a==='language')await lecture.setLanguage(lecture.language==='zh'?'en':'zh');
  else if(a==='board:lottery')await lecture.drawStudent();
  else if(a==='board:roster')await lecture.importStudentRoster();
  else if(a==='board:time')lecture.toggleTimeDisplay();
  else if(a==='board:reveal')await lecture.revealCurrent();
  else if(a==='activity:skip')await lecture.skipClassroomActivity();
  else if(a==='lectern:stow')lecture.toggleStorage();
  else if(a==='lectern:view'){const p=hall.lectern.speakerPose(camera.aspect);apply({position:p.position.toArray(),target:p.target.toArray(),fov:p.fov});follow.touch();}
  else if(a==='course:catalog')openLibrary();
  else if(a.startsWith('course:external:'))window.open('https://birationalclass.github.io/shengmeng/courses/abstract-algebra/2026-fall/?view=lesson&section='+a.slice(16),'_blank','noopener');
  else if(a==='course:manuscript')window.open(lecture.report.url,'_blank','noopener');
  else if(a.startsWith('seminar:section:')){const part=lecture.navigation?.sections?.find(s=>s.id===a.split(':')[2]);if(part){await lecture.setRange(part.start,part.end);focus();}}
  else if(a.startsWith('course:section:'))await selectReport(a.slice(15));
  else if(a.startsWith('report:'))await selectReport(a.slice(7));
  else if(a.startsWith('screen:site:')){const site=VIDEO_SITES.find(s=>s.id===a.slice(12));if(site)webview.open(site);}
  else if(a.startsWith('screen:')||a.startsWith('program:')||a.startsWith('course:')||a.startsWith('seminar:'))lecture.screenAction(a);
  updateUI();
 }catch(error){$('status').textContent=error.message;}
}
$('catalog').onclick=()=>openLibrary();$('reports').onclick=()=>openLibrary('reports');$('overview').onclick=overview;$('focus').onclick=focus;
$('play').onclick=()=>action('voice:toggle');$('previous').onclick=()=>action('board:previous');$('next').onclick=()=>action('board:next');$('closer').onclick=()=>action('camera:closer');$('farther').onclick=()=>action('camera:farther');$('language').onclick=()=>action('language');
$('page').onchange=()=>action('page:seek:'+$('page').value);$('rate').onchange=()=>lecture?.setVoiceRate(Number($('rate').value));$('fullscreen').onclick=async()=>{if(document.fullscreenElement)await document.exitFullscreen();else await document.documentElement.requestFullscreen();};
function animate(stamp){requestAnimationFrame(animate);const dt=Math.max(0,Math.min(.1,(stamp-last)/1000));last=stamp;if(document.hidden)return;
 lecture?.update(dt,reduced);hall.chairs.update(dt);
 const tracking=follow.following&&(view==='overview'||lecture?.followEnabled);
 if(tracking){const desired=view==='board'?lecture.cameraView(camera.aspect,57):hallOverview(camera.aspect);apply(motion.sample(pose(),{position:desired.position.toArray?.()||desired.position,target:desired.target.toArray?.()||desired.target,fov:desired.fov},dt,{immediate:reduced}));}else{keyboard(dt);controls.update();}
 constrainHallCamera(camera,controls.target);scene.updateMatrixWorld(true);webview.update(camera,lecture,scene);
 hall.lectern.update({playing:lecture?.playing,page:lecture?.navigationPage??0,total:lecture?.progress.total??0,seeking:lecture?.seeking,retractable:true,stored:lecture?.stored??true,storageProgress:lecture?.storageProgress??1});
 if(stamp-lastUI>200){lastUI=stamp;updateUI();}if(stamp-lastDiagnostic>250){lastDiagnostic=stamp;canvas.dataset.camera=JSON.stringify({position:camera.position.toArray(),target:controls.target.toArray(),bounds:HALL_CAMERA_BOUNDS});canvas.dataset.board=String(lecture?.navigationPage??-1);canvas.dataset.voicePhase=lecture?.voiceState.phase||'idle';canvas.dataset.voiceTime=String(lecture?.voiceState.time||0);}
 renderer.render(scene,camera);
}requestAnimationFrame(animate);
async function boot(){try{
 await Promise.all([loadMathRuntime(),loadBoardFonts()]);
 lecture=await createLecture(lectureRoot,renderer,{camera,retractable:true,startStored:true,requireSelection:true,defaultReport:'sylow-theorems',initialLanguage:'zh',floorMaterial:hall.carpetMaterial,isActive:()=>!document.hidden,onProgress:p=>{$('loadingText').textContent='准备报告厅 · '+Math.round(p*100)+'%';}});
 library=createCourseLibrary({getLecture:()=>lecture,onSelect:selectReport});
 const ray=new T.Raycaster(),pointer=new T.Vector2();
 bindPhysicalButtons(canvas,controls,event=>{const rect=canvas.getBoundingClientRect();pointer.set((event.clientX-rect.left)/rect.width*2-1,1-(event.clientY-rect.top)/rect.height*2);scene.updateMatrixWorld(true);ray.setFromCamera(pointer,camera);ray.far=25;const hit=ray.intersectObjects([...lecture.hoverTargets,...hall.lectern.targets].filter(o=>{for(let p=o;p;p=p.parent)if(!p.visible)return false;return true;}),false)[0];if(!hit)return null;hit.object.userData.action=physicalHitAction(hit,lecture.clock);return hit.object;},a=>void action(a));
 canvas.addEventListener('pointermove',()=>lecture.screenWake(),{passive:true});
 void startDeferredTextures(()=>{},{phase:'hall'});canvas.dataset.ready='true';canvas.dataset.mode='blackboard';canvas.dataset.smartScreenBackground=SMART_SCREEN_BACKGROUND;$('loading').hidden=true;$('catalog').disabled=false;$('reports').disabled=false;updateUI();
 const course=new URLSearchParams(location.search).get('course');if(course&&lecture.reports.some(r=>r.id===course))await selectReport(course);
 }catch(error){$('loadingText').textContent='报告厅准备失败：'+error.message;$('retry').hidden=false;console.error(error);}}
$('retry').onclick=()=>location.reload();void boot();
