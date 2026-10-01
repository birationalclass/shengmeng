import * as THREE from 'three';
import { OrbitControls } from '../3d/vendor/OrbitControls.js';
const $=s=>document.querySelector(s),release='20261001-gallery';
let renderer,controls,camera,terrain,meta,material,grayMaterial,geometryVersion=0,frames=0,last=performance.now();
const loading=$('#loading'),status=$('#status');
const fail=e=>{console.error(e);loading.hidden=false;status.textContent='加载未完成：'+e.message;$('#progress').hidden=true;};
try {
renderer=new THREE.WebGLRenderer({antialias:true,powerPreference:'high-performance'});renderer.setPixelRatio(Math.min(devicePixelRatio,1.5));renderer.setSize(innerWidth,innerHeight);renderer.toneMapping=THREE.ACESFilmicToneMapping;renderer.toneMappingExposure=1;$('#scene').append(renderer.domElement);
const scene=new THREE.Scene();scene.background=new THREE.Color('#7591a5');scene.fog=new THREE.Fog('#91a5b3',9000,24000);
camera=new THREE.PerspectiveCamera(40,innerWidth/innerHeight,1,50000);controls=new OrbitControls(camera,renderer.domElement);controls.enableDamping=true;controls.dampingFactor=.075;controls.rotateSpeed=.5;controls.zoomSpeed=.8;controls.minDistance=40;controls.maxDistance=16000;controls.maxPolarAngle=Math.PI*.8;controls.autoRotateSpeed=.18;
const hemisphere=new THREE.HemisphereLight('#dceaff','#534838',2);scene.add(hemisphere);const sun=new THREE.DirectionalLight('#fff1d9',3.2);scene.add(sun);
function light(){const a=THREE.MathUtils.degToRad(Number($('#sun').value));sun.position.set(Math.cos(a)*6000,3200,Math.sin(a)*6000);}light();
const views={wide:[[4300,2600,-5900],[0,700,-200]],ridge:[[1700,1600,-2400],[0,980,0]],near:[[650,1380,-750],[60,1190,-130]]};
function aim(name){const [p,t]=views[name];camera.position.set(...p);controls.target.set(...t);controls.update();document.querySelectorAll('[data-view]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.view===name)));}aim('wide');
document.querySelectorAll('[data-view]').forEach(b=>b.onclick=()=>aim(b.dataset.view));$('#sun').oninput=light;$('#exposure').oninput=e=>renderer.toneMappingExposure=Number(e.target.value);$('#rotate').onchange=e=>controls.autoRotate=e.target.checked;
const textureLoader=new THREE.TextureLoader();const rock=await textureLoader.loadAsync(new URL('assets/岩石颜色.webp',import.meta.url));rock.colorSpace=THREE.SRGBColorSpace;rock.wrapS=rock.wrapT=THREE.RepeatWrapping;rock.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());
material=new THREE.MeshStandardMaterial({color:0xffffff,roughness:.86});grayMaterial=new THREE.MeshStandardMaterial({color:'#a4aaa9',roughness:.9});
material.onBeforeCompile=shader=>{shader.uniforms.rockTexture={value:rock};shader.vertexShader=shader.vertexShader.replace('#include <common>',`#include <common>
attribute float snowDeposit;
varying vec3 terrainPosition;
varying vec3 terrainNormal;
varying float terrainSnow;`).replace('#include <begin_vertex>',`#include <begin_vertex>
terrainPosition=position;terrainNormal=normal;terrainSnow=snowDeposit;`);
shader.fragmentShader=shader.fragmentShader.replace('#include <common>',`#include <common>
uniform sampler2D rockTexture;
varying vec3 terrainPosition;
varying vec3 terrainNormal;
varying float terrainSnow;
float terrainHash(vec3 p){return fract(sin(dot(p,vec3(127.1,311.7,74.7)))*43758.5453);}
float terrainNoise(vec3 p){vec3 i=floor(p),f=fract(p);f=f*f*(3.0-2.0*f);return mix(mix(mix(terrainHash(i),terrainHash(i+vec3(1,0,0)),f.x),mix(terrainHash(i+vec3(0,1,0)),terrainHash(i+vec3(1,1,0)),f.x),f.y),mix(mix(terrainHash(i+vec3(0,0,1)),terrainHash(i+vec3(1,0,1)),f.x),mix(terrainHash(i+vec3(0,1,1)),terrainHash(i+vec3(1,1,1)),f.x),f.y),f.z);}`);
shader.fragmentShader=shader.fragmentShader.replace('#include <color_fragment>',`#include <color_fragment>
vec3 weights=pow(abs(normalize(terrainNormal)),vec3(4.0));weights/=max(weights.x+weights.y+weights.z,0.0001);
vec3 p=terrainPosition/7.0;
vec3 rockColor=texture2D(rockTexture,p.yz).rgb*weights.x+texture2D(rockTexture,p.xz).rgb*weights.y+texture2D(rockTexture,p.xy).rgb*weights.z;
float luminance=dot(rockColor,vec3(.2126,.7152,.0722));rockColor=mix(vec3(luminance),rockColor,.35)*.42;
rockColor*=mix(.58,1.0,terrainNoise(terrainPosition*.015));
float snow=smoothstep(.14,.28,terrainSnow*mix(.25,.8,terrainNoise(terrainPosition*.18)));
diffuseColor.rgb*=mix(rockColor,vec3(.78,.83,.89),snow);`);
};
$('#gray').onchange=()=>{if(terrain)terrain.material=$('#gray').checked?grayMaterial:material;};
meta=await (await fetch('terrain.json?v='+release)).json();
async function loadLevel(id){const version=++geometryVersion,level=meta.levels.find(l=>l.id===id);loading.hidden=false;$('#quality').disabled=true;status.textContent='正在读取'+(id==='detail'?'精细':'流畅')+'地形…';const progress=$('#progress');progress.hidden=false;progress.value=0;progress.max=level.bytes;
try{const response=await fetch(level.file+'?v='+release);if(!response.ok)throw new Error('地形文件 '+response.status);const reader=response.body.getReader(),chunks=[];let count=0;for(;;){const {done,value}=await reader.read();if(done)break;chunks.push(value);count+=value.byteLength;progress.value=count;}if(count!==level.bytes)throw new Error('地形数据不完整');const bytes=new Uint8Array(count);let offset=0;for(const c of chunks){bytes.set(c,offset);offset+=c.length;}const data=new Float32Array(bytes.buffer);status.textContent='正在构建山脊与材质…';await new Promise(requestAnimationFrame);
const w=level.width,h=level.height,positions=new Float32Array(w*h*3),snow=new Float32Array(w*h);for(let y=0;y<h;y++)for(let x=0;x<w;x++){const i=y*w+x;positions[i*3]=meta.origin[0]+x*level.spacing-meta.center[0];positions[i*3+1]=data[i*2]-meta.baseElevation;positions[i*3+2]=-(meta.origin[1]-y*level.spacing-meta.center[1]);snow[i]=data[i*2+1];}
const indices=new Uint32Array((w-1)*(h-1)*6);let k=0;for(let y=0;y<h-1;y++)for(let x=0;x<w-1;x++){const a=y*w+x;indices[k++]=a;indices[k++]=a+w;indices[k++]=a+w+1;indices[k++]=a;indices[k++]=a+w+1;indices[k++]=a+1;}
const geometry=new THREE.BufferGeometry();geometry.setAttribute('position',new THREE.BufferAttribute(positions,3));geometry.setAttribute('snowDeposit',new THREE.BufferAttribute(snow,1));geometry.setIndex(new THREE.BufferAttribute(indices,1));geometry.computeVertexNormals();geometry.computeBoundingSphere();if(version!==geometryVersion){geometry.dispose();return;}if(terrain){scene.remove(terrain);terrain.geometry.dispose();}terrain=new THREE.Mesh(geometry,$('#gray').checked?grayMaterial:material);scene.add(terrain);await renderer.compileAsync(scene,camera);renderer.render(scene,camera);loading.hidden=true;$('#stats').dataset.summary=`${level.spacing} 米网格 · ${(indices.length/3).toLocaleString('zh-CN')} 三角面<br>地形数据 ${(count/1048576).toFixed(1)} MiB · 最高采样 4477 m`;$('#stats').innerHTML=$('#stats').dataset.summary;last=performance.now();frames=0;
}catch(e){fail(e);}finally{$('#quality').disabled=false;}}
$('#quality').onchange=e=>loadLevel(e.target.value);await loadLevel('standard');
addEventListener('resize',()=>{camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();renderer.setSize(innerWidth,innerHeight);});renderer.domElement.addEventListener('webglcontextlost',e=>{e.preventDefault();fail(new Error('显卡上下文丢失，请刷新或切换流畅模式。'));});
renderer.setAnimationLoop(()=>{if(document.hidden)return;controls.update();renderer.render(scene,camera);frames++;const now=performance.now();if(now-last>1000){if($('#stats').dataset.summary)$('#stats').innerHTML=$('#stats').dataset.summary+`<br>${Math.round(frames*1000/(now-last))} FPS`;last=now;frames=0;}});
}catch(e){fail(e);}
const dialog=$('#sample-dialog');$('#samples').onclick=()=>dialog.showModal();$('#close-samples').onclick=()=>dialog.close();document.querySelectorAll('[data-shot]').forEach(b=>b.onclick=()=>{const name=b.dataset.shot;$('#sample-image').src='assets/'+name+'.webp';$('#sample-image').alt=name+'渲染样片';document.querySelectorAll('[data-shot]').forEach(q=>q.setAttribute('aria-pressed',String(q===b)));});
