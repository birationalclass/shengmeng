import {planetMotion} from './celestial-motion.mjs?v=orbits-46';
import * as T from '../../../visuals/3d/vendor/three.module.js';
import {galaxyBlackHole} from './galaxy-black-hole.mjs?v=scene-hole-3';
import {detailedStar} from './stellar-render.mjs?v=corona-50';
import {detailedPlanet} from './planet-render.mjs?v=orbits-46';
const canvas=document.querySelector('canvas'),renderer=new T.WebGLRenderer({canvas,antialias:true,alpha:true});renderer.setPixelRatio(Math.min(devicePixelRatio,2));renderer.outputColorSpace=T.SRGBColorSpace;
const scene=new T.Scene(),camera=new T.PerspectiveCamera(40,1,.1,200),sphere=new T.SphereGeometry(1,96,64),stage=new T.Group();scene.add(stage);
const bh=galaxyBlackHole(sphere);bh.scale.setScalar(.544*2);bh.position.x=-6;stage.add(bh);
let star,planet,angle=.1,tilt=.25,distance=22,time=0,paused=false,large=false;
function remove(body){if(!body)return;stage.remove(body);body.traverse(o=>{if(o.geometry&&o.geometry!==sphere)o.geometry.dispose();if(o.material)o.material.dispose();});}
function setStar(type){remove(star);star=detailedStar(sphere,{type},4);star.scale.setScalar(.544*.8*2);stage.add(star);}
function setPlanet(kind){remove(planet);planet=detailedPlanet(sphere,kind,9);planet.userData.motion=planetMotion(['ocean-planet','gas-planet','ice-planet','ring-planet'][kind],9);planet.scale.setScalar(.544*.6);planet.position.x=large?5.2:6;stage.add(planet);}
setStar('gold-star');setPlanet(0);
function resize(){renderer.setSize(innerWidth,innerHeight,false);camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();}addEventListener('resize',resize);resize();
document.querySelectorAll('[data-star]').forEach(b=>b.onclick=()=>{setStar(b.dataset.star);document.querySelectorAll('[data-star]').forEach(x=>x.setAttribute('aria-pressed',String(x===b)));});
document.querySelectorAll('[data-planet]').forEach(b=>b.onclick=()=>{setPlanet(Number(b.dataset.planet));document.querySelectorAll('[data-planet]').forEach(x=>x.setAttribute('aria-pressed',String(x===b)));});
let en=false;const strings=['Golden star','Blue-white star','Red star','Ocean planet','Gas planet','Ice planet','Ringed planet'],zh=['金色恒星','蓝白恒星','红色恒星','海洋行星','气态行星','冰岩行星','土星环行星'];
document.querySelector('#lang').onclick=()=>{en=!en;document.documentElement.lang=en?'en':'zh-CN';document.querySelector('h1').textContent=en?'Celestial model laboratory':'星体 · 模型实验室';document.querySelector('#hint').textContent=en?'Drag to orbit · Scroll to zoom · Uncapped animation':'拖动环绕 · 滚轮缩放 · 不限制帧率';document.querySelectorAll('nav button').forEach((b,i)=>b.textContent=(en?strings:zh)[i]);document.querySelector('#lang').textContent=en?'中文':'EN';document.querySelector('#scale').textContent=en?'Detail / Actual size':'细节 / 实际尺寸';document.querySelector('#names').innerHTML=(en?['Black hole','Star','Planet']:['黑洞','恒星','行星']).map((s,i)=>`<span>${s}<small>${[100,80,30][i]}%</small></span>`).join('');};
document.querySelector('#pause').onclick=()=>{paused=!paused;document.querySelector('#pause').textContent=paused?'▶':'Ⅱ';};
document.querySelector('#scale').onclick=()=>{large=!large;stage.scale.setScalar(large?1.3:1);bh.position.x=large?-5.2:-6;planet.position.x=large?5.2:6;};
let drag;canvas.onpointerdown=e=>{drag={x:e.clientX,y:e.clientY};canvas.setPointerCapture(e.pointerId);};canvas.onpointermove=e=>{if(!drag)return;angle+=(e.clientX-drag.x)*.005;tilt=Math.max(-.8,Math.min(.8,tilt+(e.clientY-drag.y)*.004));drag={x:e.clientX,y:e.clientY};};canvas.onpointerup=()=>drag=null;canvas.onwheel=e=>{e.preventDefault();distance=Math.max(8,Math.min(30,distance+e.deltaY*.01));};
let last=performance.now();function frame(now){requestAnimationFrame(frame);const dt=Math.min(.04,(now-last)/1000);last=now;if(document.hidden)return;if(!paused)time+=dt;const dist=Math.max(distance,11/camera.aspect);camera.position.set(Math.sin(angle)*dist,Math.sin(tilt)*dist,Math.cos(angle)*Math.cos(tilt)*dist);camera.lookAt(0,0,0);star.rotation.y=-time*.15;planet.rotation.order="ZYX";planet.rotation.y=-time*planet.userData.motion.spin;[bh,star,planet].forEach(p=>p.userData.effects?.forEach(m=>m.uniforms.time.value=time));scene.updateMatrixWorld(true);camera.updateMatrixWorld(true);star.getWorldPosition(planet.userData.hostLight.value);bh.userData.updateBlackHole(renderer,camera);renderer.render(scene,camera);}requestAnimationFrame(frame);
