import * as THREE from 'three';
import {OrbitControls} from '../3d/vendor/OrbitControls.js';
import {installCoastWalks,walkProgress} from './coast-walks.js';
import {classroomBreakTime,classroomBreakHour} from './classroom-beach-time.js';
import {CLASSROOM_BEACH_ROUTES} from './classroom-beach-break.js';
import {createArrivalEnvironment} from './scene.js?v=demand-1';
import {startDeferredTextures} from './deferred-textures.js?v=demand-1';
const query=new URLSearchParams(location.search),token=query.get('token'),route=CLASSROOM_BEACH_ROUTES.find(r=>r.id===query.get('route'))||CLASSROOM_BEACH_ROUTES[0];
const tell=(type,extra={})=>parent.postMessage({type,token,...extra},location.origin);
let startHour=Number(query.get('hour')??classroomBreakHour()),duration=300,elapsed=0,running=false,lastClock=performance.now(),renderer,environment,frame;
addEventListener('message',event=>{if(event.origin!==location.origin||event.source!==parent||event.data?.type!=='refuge-classroom-break-clock'||event.data.token!==token)return;elapsed=Math.max(0,Number(event.data.elapsed)||0);startHour=Number(event.data.startHour??startHour);duration=Number(event.data.duration)||300;running=Boolean(event.data.playing);lastClock=performance.now();});
async function start(){
 const canvas=document.getElementById('coast'),scene=new THREE.Scene(),camera=new THREE.PerspectiveCamera(60,innerWidth/innerHeight,.2,12000),shots=[];
 installCoastWalks(shots);const shot=shots.find(s=>s.name===route.name),positions=new THREE.CatmullRomCurve3(shot.positions.map(p=>new THREE.Vector3(...p)),false,'centripetal'),targets=new THREE.CatmullRomCurve3(shot.targets.map(p=>new THREE.Vector3(...p)),false,'centripetal');
 renderer=new THREE.WebGLRenderer({canvas,antialias:false,powerPreference:'low-power'});renderer.setPixelRatio(Math.min(devicePixelRatio,1.5));renderer.setSize(innerWidth,innerHeight);renderer.outputColorSpace=THREE.SRGBColorSpace;renderer.toneMapping=THREE.ACESFilmicToneMapping;renderer.toneMappingExposure=1;
 // This is the existing coastal terrain, ocean and route geometry. The separate
 // classroom view needs no buildings, lecture textures or second course player.
 const date=new Date();environment=await createArrivalEnvironment(renderer,scene,()=>{},{noiseSize:32,atmosphereSize:128,cloudSize:384,cloudSteps:24,cloudInterval:650},{date,hour:startHour,weather:{cloud:.5,wind:8,rain:0}});
 await startDeferredTextures(()=>{},{phase:'entry'});environment.study.setQuality(0);environment.study.settings.tide=.9;environment.sky.userData.setCloudQuality('low');await environment.sky.userData.prepareClouds(()=>{},()=>Promise.resolve(),'low');
 const controls=new OrbitControls(camera,canvas);controls.enableDamping=true;controls.enablePan=false;let manual=false;controls.addEventListener('start',()=>{manual=true;});
 const pose=t=>{const p=walkProgress(Math.min(t,shot.duration),shot.duration);camera.position.copy(positions.getPointAt(p));controls.target.copy(targets.getPointAt(p));camera.lookAt(controls.target);};
 pose(elapsed);environment.setTime(startHour,date,0,.5);for(let i=0;i<32;i++)environment.sky.userData.updateAtmosphere(.1);environment.setTime(startHour,date,0,.5);environment.study.update(camera,0);renderer.render(scene,camera);canvas.dataset.route=route.id;canvas.dataset.ready='true';tell('refuge-classroom-beach-ready',{route:route.id});
 let previous=performance.now();function draw(stamp){const dt=Math.min(.05,Math.max(0,(stamp-previous)/1000));previous=stamp;const t=elapsed+(running?(stamp-lastClock)/1000:0);if(!manual)pose(t);else controls.update();environment.ocean.material.uniforms.time.value+=running?dt:0;environment.study.settings.paused=!running;environment.study.update(camera,running?dt:0);const cycle=classroomBreakTime(startHour,t,duration);environment.setTime(cycle.sceneHour,new Date(+date+cycle.dayOffset*86400000),running?dt:0,cycle.cloudCoverage);renderer.render(scene,camera);canvas.dataset.hour=cycle.sceneHour.toFixed(6);canvas.dataset.dayHours=cycle.dayHours.toFixed(6);canvas.dataset.timeRate=String(cycle.timeRate);canvas.dataset.cloud=String(environment.sky.material.uniforms.cloud.value);canvas.dataset.cloudVisible=String(environment.sky.material.uniforms.useVolumeClouds.value);canvas.dataset.daylight=String(environment.sky.material.uniforms.day.value);canvas.dataset.walkTime=t.toFixed(2);canvas.dataset.position=camera.position.toArray().join(',');frame=requestAnimationFrame(draw);}frame=requestAnimationFrame(draw);
 addEventListener('resize',()=>{camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();renderer.setSize(innerWidth,innerHeight);});
 addEventListener('pagehide',()=>{cancelAnimationFrame(frame);controls.dispose();environment.study.dispose();renderer.dispose();},{once:true});
}
start().catch(error=>{document.getElementById('coast').dataset.error=error.message;tell('refuge-classroom-beach-error',{error:error.message});console.error(error);});
