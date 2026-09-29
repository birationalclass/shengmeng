import * as T from '../../../visuals/3d/vendor/three.module.js';
import {COSMIC_PALETTES,dustTint} from './cosmic-palettes.mjs?v=nebula-73';
import {galaxyBlackHole} from './galaxy-black-hole.mjs?v=nebula-73';
import {addNebula,dustField} from './galaxy-dust.mjs?v=nebula-73';
import {watchPageActivity} from './page-activity.mjs?v=nebula-70';
const canvas=document.querySelector('canvas'),renderer=new T.WebGLRenderer({canvas,antialias:true}),scene=new T.Scene(),camera=new T.PerspectiveCamera(46,1,.1,300),root=new T.Group();
renderer.setPixelRatio(Math.min(devicePixelRatio,1.7));renderer.setClearColor(0x040711);scene.add(root);root.rotation.z=-.15;
const hole=galaxyBlackHole(new T.SphereGeometry(1,32,24));hole.traverse(p=>{if(p.material?.depthWrite)p.renderOrder=-50;});root.add(hole);
const inner=6,outer=17,cloud=addNebula(T,root,'S4',inner,outer),field=dustField('S4',14000,inner,outer),geo=new T.BufferGeometry();
geo.setAttribute('position',new T.Float32BufferAttribute(field.positions,3));geo.setAttribute('color',new T.Float32BufferAttribute(field.colors,3));
const points=new T.Points(geo,new T.PointsMaterial({size:.035,vertexColors:true,transparent:true,opacity:.65,depthWrite:false,blending:T.AdditiveBlending}));root.add(points);
function choose(p){hole.userData.setPalette(p);cloud.userData.setPalette(p);const colors=geo.attributes.color;for(let i=0;i<colors.count;i++){const j=i*3,u=(Math.hypot(field.positions[j],field.positions[j+2])-inner)/(outer-inner),c=dustTint(p,u);colors.setXYZ(i,...c.map(x=>x*(.4+.25*((i*37%101)/101))));}colors.needsUpdate=true;document.getElementById('paletteName').textContent=p.name;document.querySelectorAll('#palettes button').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.id===p.id)));}
for(const p of COSMIC_PALETTES){const b=document.createElement('button');b.dataset.id=p.id;b.innerHTML='<i></i>'+p.name;b.querySelector('i').style.background='linear-gradient(90deg,'+p.hot+','+p.mid+','+p.outer+','+p.edge+')';b.onclick=()=>choose(p);document.getElementById('palettes').append(b);}
choose(COSMIC_PALETTES[0]);
function resize(){const w=innerWidth,h=innerHeight,mobile=w<700;renderer.setSize(w,h,false);camera.aspect=w/h;camera.position.set(0,mobile?22:15,mobile?53:40);camera.lookAt(mobile?0:3,mobile?-4:0,0);camera.updateProjectionMatrix();}addEventListener('resize',resize);resize();
let active=true,paused=false,last=performance.now(),time=0;watchPageActivity(v=>{active=v;last=performance.now();});
document.getElementById('pause').onclick=e=>{paused=!paused;e.currentTarget.textContent=paused?'继续旋转':'暂停旋转';e.currentTarget.setAttribute('aria-pressed',String(paused));};
function frame(now){requestAnimationFrame(frame);const dt=Math.min(.04,(now-last)/1000);last=now;if(!active)return;if(!paused){time+=dt;root.rotation.y=-time*.035;points.rotation.y=-time*.018;cloud.rotation.y=points.rotation.y;}hole.userData.effects.forEach(m=>m.uniforms.time.value=time);scene.updateMatrixWorld(true);camera.updateMatrixWorld(true);hole.userData.updateBlackHole(renderer,camera);renderer.render(scene,camera);}requestAnimationFrame(frame);

