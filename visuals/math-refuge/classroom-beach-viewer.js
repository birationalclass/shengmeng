import * as THREE from 'three';
import {installCoastWalks,walkProgress} from './coast-walks.js';
import {classroomBreakTime,classroomBreakHour,CLASSROOM_BREAK_CLOUD} from './classroom-beach-time.js?v=break-cloud20-20261024';
import {CLASSROOM_BEACH_ROUTES} from './classroom-beach-break.js';
import {createArrivalEnvironment,createRetreat} from './scene.js?v=classroom-beach-day-20261023';
import {finishCampusLayout,buildingOffset} from './campus-layout.js';
import {BUILDING_SCALE as S,HALL} from './site-layout.js';
import {classroomBoardPose,createClassroomBeachFlight} from './classroom-beach-camera.js';
import {startDeferredTextures} from './deferred-textures.js?v=demand-1';
const query=new URLSearchParams(location.search),token=query.get('token'),route=CLASSROOM_BEACH_ROUTES.find(r=>r.id===query.get('route'))||CLASSROOM_BEACH_ROUTES[0];
const tell=(type,extra={})=>parent.postMessage({type,token,...extra},location.origin);
let startHour=Number(query.get('hour')??classroomBreakHour()),duration=300,elapsed=0,running=true,phase='departing',lastClock=performance.now(),renderer,environment,frame,boardMaterial,imageURL;
function setBoardImage(url){if(!url)return;imageURL=url;if(boardMaterial)new THREE.TextureLoader().load(url,map=>{map.colorSpace=THREE.SRGBColorSpace;boardMaterial.map=map;boardMaterial.needsUpdate=true;});}
addEventListener('message',event=>{
 if(event.origin!==location.origin||event.source!==parent||event.data?.token!==token)return;
 if(event.data.type==='refuge-classroom-beach-image'){setBoardImage(event.data.image);return;}
 if(event.data.type!=='refuge-classroom-break-clock')return;
 elapsed=Math.max(0,Number(event.data.elapsed)||0);startHour=Number(event.data.startHour??startHour);duration=Number(event.data.duration)||300;running=Boolean(event.data.playing);phase=event.data.phase;lastClock=performance.now();
});
tell('refuge-classroom-beach-image-request');
async function start(){
 const canvas=document.getElementById('coast'),scene=new THREE.Scene(),camera=new THREE.PerspectiveCamera(60,innerWidth/innerHeight,.2,12000),shots=[];
 installCoastWalks(shots);const shot=shots.find(s=>s.name===route.name),positions=new THREE.CatmullRomCurve3(shot.positions.map(p=>new THREE.Vector3(...p)),false,'centripetal'),targets=new THREE.CatmullRomCurve3(shot.targets.map(p=>new THREE.Vector3(...p)),false,'centripetal');
 renderer=new THREE.WebGLRenderer({canvas,antialias:false,powerPreference:'low-power'});renderer.setPixelRatio(Math.min(devicePixelRatio,1.25));renderer.setSize(innerWidth,innerHeight);renderer.outputColorSpace=THREE.SRGBColorSpace;renderer.toneMapping=THREE.ACESFilmicToneMapping;renderer.toneMappingExposure=1;
 const date=new Date(),arrival=await createArrivalEnvironment(renderer,scene,()=>{},{noiseSize:32,atmosphereSize:128,cloudSize:384,cloudSteps:24,cloudInterval:650},{date,hour:startHour,weather:{cloud:CLASSROOM_BREAK_CLOUD,wind:8,rain:0}});
 // Reuse the real campus and hall so the camera exits through a doorway.
 // The board is a local still from the parent; no second lesson or voice player.
 environment=await createRetreat(renderer,scene,()=>{},{},{environment:arrival,date,hour:startHour});finishCampusLayout(scene,environment,[]);
 await startDeferredTextures(()=>{},{phase:'entry'});await startDeferredTextures(()=>{},{phase:'hall'});
 const study=environment.ocean.userData.study;study.setQuality(0);study.settings.tide=.9;environment.sky.userData.setCloudQuality('low');await environment.sky.userData.prepareClouds(()=>{},()=>Promise.resolve(),'low');
 const o=buildingOffset('01B');boardMaterial=new THREE.MeshBasicMaterial({color:0xffffff});const board=new THREE.Mesh(new THREE.PlaneGeometry(5.28,2.2),boardMaterial);board.position.set(HALL.boardX*S+o.x-.035,2.35,o.z);board.rotation.y=-Math.PI/2;scene.add(board);if(imageURL)setBoardImage(imageURL);else boardMaterial.color.set('#063323');
 const boardPose=classroomBoardPose(camera.aspect),coastPose={position:positions.getPointAt(0).toArray(),target:targets.getPointAt(0).toArray(),fov:shot.fov||60};
 let flight=createClassroomBeachFlight(boardPose,coastPose),flightSeconds=0,mode='departing';
 const apply=pose=>{camera.position.fromArray(pose.position);camera.quaternion.fromArray(pose.quaternion);camera.fov=pose.fov;camera.updateProjectionMatrix();};
 apply(flight.sample(0));environment.setTime(startHour,false,0,1,date,{cloudCoverage:CLASSROOM_BREAK_CLOUD});for(let i=0;i<32;i++)environment.sky.userData.updateAtmosphere(.1);study.update(camera,0);renderer.render(scene,camera);
 canvas.dataset.route=route.id;canvas.dataset.prepared='true';tell('refuge-classroom-beach-prepared',{route:route.id});
 let previous=performance.now();function draw(stamp){
  const dt=Math.min(.1,Math.max(0,(stamp-previous)/1000));previous=stamp;
  if(phase==='returning'&&mode!=='returning'&&mode!=='returned'){
   const target=camera.position.clone().add(new THREE.Vector3(0,0,-25).applyQuaternion(camera.quaternion));
   flight=createClassroomBeachFlight(boardPose,{position:camera.position.toArray(),target:target.toArray(),quaternion:camera.quaternion.toArray(),fov:camera.fov},{returning:true});flightSeconds=0;mode='returning';
  }
  const t=mode==='resting'?Math.min(duration,elapsed+(running?(stamp-lastClock)/1000:0)):elapsed;
  if(mode==='departing'||mode==='returning'){
   if(running)flightSeconds=Math.min(flight.duration,flightSeconds+dt);apply(flight.sample(flightSeconds));
   if(flightSeconds>=flight.duration){if(mode==='departing'){mode='resting';canvas.dataset.ready='true';tell('refuge-classroom-beach-ready',{route:route.id});}else{mode='returned';tell('refuge-classroom-beach-returned');}}
  }else if(mode==='resting'){
   const p=walkProgress(Math.min(t,shot.duration),shot.duration);camera.position.copy(positions.getPointAt(p));camera.lookAt(targets.getPointAt(p));
  }
  environment.ocean.material.uniforms.time.value+=running?dt:0;study.settings.paused=!running;study.update(camera,running?dt:0);environment.campus.automaticDoors?.update(running?dt:0,false,[camera.position,...((mode==='departing'||mode==='returning')?[new THREE.Vector3(...flight.sample(Math.min(flight.duration,flightSeconds+1.2)).position)]:[])]);
  const cycle=classroomBreakTime(startHour,t,duration);environment.setTime(cycle.sceneHour,false,running?dt:0,cycle.timeRate,new Date(+date+cycle.dayOffset*86400000),{cloudCoverage:cycle.cloudCoverage});
  renderer.render(scene,camera);Object.assign(canvas.dataset,{phase:mode,flightSeconds:flightSeconds.toFixed(3),hour:cycle.sceneHour.toFixed(6),dayHours:cycle.dayHours.toFixed(6),timeRate:String(cycle.timeRate),cloud:String(environment.sky.material.uniforms.cloud.value),cloudVisible:String(environment.sky.material.uniforms.useVolumeClouds.value),daylight:String(environment.sky.material.uniforms.day.value),walkTime:t.toFixed(2),position:camera.position.toArray().join(',')});frame=requestAnimationFrame(draw);
 }frame=requestAnimationFrame(draw);
 addEventListener('resize',()=>{camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();renderer.setSize(innerWidth,innerHeight);});
 addEventListener('pagehide',()=>{cancelAnimationFrame(frame);environment.dispose();renderer.dispose();},{once:true});
}
start().catch(error=>{document.getElementById('coast').dataset.error=error.message;tell('refuge-classroom-beach-error',{error:error.message});console.error(error);});
