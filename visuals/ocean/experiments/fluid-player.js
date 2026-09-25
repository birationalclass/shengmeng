import * as THREE from '../../3d/vendor/three.module.js';
const $=id=>document.getElementById(id);
const variant=new URLSearchParams(location.search).get('variant')==='breaker'?'breaker-cache':'beach-cache';
if(variant==='breaker-cache')document.querySelector('h1').textContent='三维流体 · 强推浪水槽';
const renderer=new THREE.WebGLRenderer({canvas:$('view'),antialias:true});
renderer.setPixelRatio(Math.min(devicePixelRatio,1.5));
renderer.toneMapping=THREE.ACESFilmicToneMapping;renderer.toneMappingExposure=1.1;
const scene=new THREE.Scene(),camera=new THREE.PerspectiveCamera(48,1,.05,300);
scene.background=new THREE.Color('#adcbdb');scene.fog=new THREE.Fog('#adcbdb',35,120);
scene.add(new THREE.HemisphereLight(0xdcefff,0x8e7757,2));
const sun=new THREE.DirectionalLight(0xffedcd,3.2);sun.position.set(-8,10,-5);scene.add(sun);
const envScene=new THREE.Scene();
const envMat=new THREE.ShaderMaterial({side:THREE.BackSide,uniforms:{},vertexShader:'varying vec3 p;void main(){p=position;gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.);}',fragmentShader:'varying vec3 p;void main(){vec3 d=normalize(p);vec3 c=mix(vec3(.82,.87,.88),vec3(.20,.43,.67),smoothstep(0.,.8,d.y));if(d.y<0.)c=mix(vec3(.25,.23,.18),c,exp(d.y*12.));float s=max(0.,dot(d,normalize(vec3(-.6,.65,-.4))));c+=vec3(3.,2.5,1.7)*pow(s,700.)+vec3(.4,.28,.15)*pow(s,16.);gl_FragColor=vec4(c,1.);}'});
envScene.add(new THREE.Mesh(new THREE.SphereGeometry(80,32,16),envMat));
const pmrem=new THREE.PMREMGenerator(renderer),env=pmrem.fromScene(envScene,.04);scene.environment=env.texture;pmrem.dispose();envMat.dispose();
const sandGeo=new THREE.PlaneGeometry(12,5,80,32);sandGeo.rotateX(-Math.PI/2);
const pos=sandGeo.attributes.position;
for(let i=0;i<pos.count;i++)pos.setY(i,-1.7+.19*(pos.getX(i)+6));sandGeo.computeVertexNormals();
const sand=new THREE.Mesh(sandGeo,new THREE.MeshStandardMaterial({color:0xb7a27d,roughness:.86,side:THREE.DoubleSide}));scene.add(sand);
const bedBase=new THREE.BufferGeometry();
bedBase.setAttribute('position',new THREE.Float32BufferAttribute([-6,-1.71,-2.5,6,.57,-2.5,6,.57,2.5,-6,-1.71,2.5,-6,-2,-2.5,6,-2,-2.5,6,-2,2.5,-6,-2,2.5],3));
bedBase.setIndex([0,1,5,0,5,4,1,2,6,1,6,5,2,3,7,2,7,6,3,0,4,3,4,7,4,5,6,4,6,7]);bedBase.computeVertexNormals();
scene.add(new THREE.Mesh(bedBase,new THREE.MeshStandardMaterial({color:0x8b816f,roughness:.9,side:THREE.DoubleSide})));
const waterMat=new THREE.MeshPhysicalMaterial({color:0xb6e3df,roughness:.13,metalness:0,transmission:.86,thickness:.7,ior:1.333,attenuationColor:0x62bdba,attenuationDistance:2.5,side:THREE.DoubleSide});
const water=new THREE.Mesh(new THREE.BufferGeometry(),waterMat);water.frustumCulled=false;scene.add(water);
const foamMat=new THREE.ShaderMaterial({transparent:true,depthWrite:false,uniforms:{height:{value:800}},vertexShader:'uniform float height;void main(){vec4 p=modelViewMatrix*vec4(position,1.);gl_Position=projectionMatrix*p;gl_PointSize=clamp(height*.016/max(.2,-p.z),1.,8.);}',fragmentShader:'void main(){vec2 p=gl_PointCoord*2.-1.;float r=dot(p,p);if(r>1.)discard;float shade=.78+.22*sqrt(1.-r);gl_FragColor=vec4(vec3(.94,.98,1.)*shade,.78*(1.-smoothstep(.6,1.,r)));}'});
const foam=new THREE.Points(new THREE.BufferGeometry(),foamMat);foam.frustumCulled=false;scene.add(foam);
let manifest,cache=new Map(),pending=new Map(),current=-1,clock=0,paused=false,active=true,last=0,angle=.62,elevation=.30,radius=10,pointer;
function cameraUpdate(){const fitted=radius*Math.max(1,.9/camera.aspect);camera.position.set(1+Math.cos(angle)*fitted,Math.sin(elevation)*fitted,Math.sin(angle)*fitted);camera.lookAt(1,-.1,0);}
function resize(){renderer.setSize(innerWidth,innerHeight,false);camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();foamMat.uniforms.height.value=renderer.domElement.height;cameraUpdate();}
resize();addEventListener('resize',resize);
function decode(buffer){
 const dv=new DataView(buffer);let off=12;const nv=dv.getUint32(0,true),ni=dv.getUint32(4,true),np=dv.getUint32(8,true);
 if(nv<20||nv>2000000||ni%3||12+nv*6+ni*4+np*12!==buffer.byteLength)throw Error('模拟帧数据无效');
 const p=new Float32Array(nv*3);
 for(let i=0;i<nv;i++){const x=dv.getUint16(off,true)*.001;const y=dv.getUint16(off+2,true)*.001-2.5;const z=dv.getUint16(off+4,true)*.001-1.8;off+=6;p.set([x-6,z,-y],i*3);}
 const idx=new Uint32Array(ni);for(let i=0;i<ni;i++,off+=4)idx[i]=dv.getUint32(off,true);
 const particles=new Float32Array(np*3);for(let i=0;i<np;i++,off+=12)particles.set([dv.getFloat32(off,true)-6,dv.getFloat32(off+8,true),-dv.getFloat32(off+4,true)],i*3);
 return {p,idx,particles};
}
async function load(i){
 if(cache.has(i))return cache.get(i);if(pending.has(i))return pending.get(i);
 const task=(async()=>{const res=await fetch('./'+variant+'/'+manifest.frames[i].file);if(!res.ok)throw Error('模拟帧读取失败');const buffer=await new Response(res.body.pipeThrough(new DecompressionStream('gzip'))).arrayBuffer();const frame=decode(buffer);cache.set(i,frame);if(cache.size>14){for(const key of cache.keys()){if(key!==current&&key!==i){cache.delete(key);break;}}}return frame;})();
 pending.set(i,task);try{return await task;}finally{pending.delete(i);}
}
function show(i){
 const f=cache.get(i);if(!f||i===current)return;
 const geo=new THREE.BufferGeometry();geo.setAttribute('position',new THREE.BufferAttribute(f.p,3));geo.setIndex(new THREE.BufferAttribute(f.idx,1));geo.computeVertexNormals();water.geometry.dispose();water.geometry=geo;
 const pg=new THREE.BufferGeometry();pg.setAttribute('position',new THREE.BufferAttribute(f.particles,3));foam.geometry.dispose();foam.geometry=pg;current=i;
 $('status').textContent=`${(f.idx.length/3).toLocaleString()} 三角面 · ${f.particles.length/3} 泡沫/飞沫粒子`;
 renderer.domElement.dataset.frame=String(i);renderer.domElement.dataset.particles=String(f.particles.length/3);
}
function fail(e){$('error').textContent=e.message;paused=true;$('play').textContent='继续';console.error(e);}
function tick(now){
 const dt=last?Math.min(.1,(now-last)/1000):0;last=now;
 if(active&&manifest){
  const i=Math.min(manifest.frames.length-1,Math.floor(clock*manifest.fps));
  if(cache.has(i)){
   show(i);if(!paused)clock+=dt*Number($('speed').value);
   if(clock>=manifest.duration){clock=manifest.duration;paused=true;$('play').textContent='重播';}
  }else load(i).catch(fail);
  for(let k=1;k<=3;k++)if(i+k<manifest.frames.length&&!pending.has(i+k)&&!cache.has(i+k))load(i+k).catch(fail);
  $('timeline').value=clock;$('time').textContent=clock.toFixed(2)+' s';renderer.render(scene,camera);
 }
 requestAnimationFrame(tick);
}
$('play').onclick=()=>{if(manifest&&clock>=manifest.duration)clock=0;paused=!paused;$('play').textContent=paused?'继续':'暂停';};
$('timeline').oninput=e=>{clock=+e.target.value;paused=true;$('play').textContent='继续';};
$('foam').onchange=e=>foam.visible=e.target.checked;$('wire').onchange=e=>waterMat.wireframe=e.target.checked;
$('reset').onclick=()=>{angle=.62;elevation=.30;radius=10;cameraUpdate();};
$('view').onpointerdown=e=>{pointer={id:e.pointerId,x:e.clientX,y:e.clientY};e.target.setPointerCapture(e.pointerId);};
$('view').onpointermove=e=>{if(!pointer||pointer.id!==e.pointerId)return;angle-=(e.clientX-pointer.x)*.006;elevation=Math.max(.05,Math.min(1.25,elevation+(e.clientY-pointer.y)*.004));pointer.x=e.clientX;pointer.y=e.clientY;cameraUpdate();};
$('view').onpointerup=$('view').onpointercancel=()=>pointer=null;
$('view').addEventListener('wheel',e=>{e.preventDefault();radius=Math.max(4,Math.min(25,radius+e.deltaY*.01));cameraUpdate();},{passive:false});
addEventListener('message',e=>{if(e.origin===location.origin&&e.source===parent&&e.data?.type==='ocean-experiment-visibility'){active=!!e.data.active;last=0;}});
try{const r=await fetch('./'+variant+'/manifest.json');if(!r.ok)throw Error('模拟缓存尚未就绪');manifest=await r.json();$('timeline').max=manifest.duration;await load(0);show(0);requestAnimationFrame(tick);}catch(e){fail(e);}
