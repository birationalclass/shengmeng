import * as THREE from 'three';
import { OrbitControls } from './vendor/OrbitControls.js';
import { GLTFExporter } from './vendor/GLTFExporter.js';
import { createRelief, updateReliefPositions, createDemo } from './geometry.js?v=20260919-2';

const $ = (id) => document.getElementById(id);
const reducedMotion = matchMedia('(prefers-reduced-motion: reduce)');
const ui = Object.fromEntries(['scene','viewer','imageInput','dropZone','sourceThumb','sourceName','sourceMeta','generateButton','progressWrap','progress','status','loadingVeil','loadingText','depthControl','detailControl','depthValue','detailValue','motionToggle','invertToggle','originalOverlay','sceneBadge','sceneTitle','sceneInfo','meshStats','compareButton'].map(id => [id,$(id)]));
let renderer, controls, camera, scene, mesh, points, worker, job = 0, timer;
let source, depth, sourceURL, texture, depthTexture, imageData, originalFile = null, busy = false;
let mode = 'texture', geometry, version = 0, frameTime = 0, pausedUntil = 0;
let distance = 6.1;
let relief, updatePending=false, interacting=false, dirty=true, inView=true;
let geometryBuilds=0, positionUpdates=0;
const group = new THREE.Group();
function status(message, error = false) { ui.status.textContent = message; ui.status.classList.toggle('error', error); }
function setBusy(value) {
  busy = value; ui.progressWrap.hidden = !value; ui.loadingVeil.hidden = !value;
  ui.generateButton.disabled = value || !originalFile || !renderer;
  ui.imageInput.disabled = value; $('demoButton').disabled = value;
  ui.viewer.setAttribute('aria-busy', String(value));
}
function stopWorker() { job++; clearTimeout(timer); worker?.terminate(); worker = null; setBusy(false); }
function releaseSource() {
  if (sourceURL) URL.revokeObjectURL(sourceURL);
  sourceURL = null; texture?.dispose(); depthTexture?.dispose();
}
function resetView() {
  camera.position.set(0,0,distance); controls.target.set(0,0,0); controls.update();
  group.rotation.set(0,0,0); pausedUntil = performance.now() + 1800;
  dirty=true;
}
function depthCanvas() {
  const canvas = document.createElement('canvas'); canvas.width=depth.width; canvas.height=depth.height;
  const ctx=canvas.getContext('2d'), image=ctx.createImageData(depth.width,depth.height);
  for (let i=0;i<depth.values.length;i++) {
    const value=Math.round((ui.invertToggle.checked ? 1-depth.values[i] : depth.values[i])*255);
    image.data.set([value,value,value,255],i*4);
  }
  ctx.putImageData(image,0,0); return canvas;
}
function updateMode() {
  mesh.material.map=mode==='depth' ? depthTexture : texture;
  mesh.material.needsUpdate=true;
  points.visible=mode==='points';mesh.visible=!points.visible;dirty=true;
}
function updatePositions() {
  if(!relief) return;
  updateReliefPositions(relief,Number(ui.depthControl.value)/100,ui.invertToggle.checked,distance);
  geometry.attributes.position.needsUpdate=true;
  geometry.computeBoundingSphere();points.geometry.boundingSphere=geometry.boundingSphere;
  ui.scene.dataset.positionUpdates=String(++positionUpdates);dirty=true;
}
function schedulePositions() {
  if(updatePending)return;
  updatePending=true;
  requestAnimationFrame(()=>{updatePending=false;updatePositions();});
}
function rebuild() {
  if (!source || !depth || !renderer) return;
  const data = createRelief(depth, source.width/source.height, Number(ui.detailControl.value), Number(ui.depthControl.value)/100, ui.invertToggle.checked, distance, $('edgeToggle').checked);
  relief=data;
  const next = new THREE.BufferGeometry();
  next.setAttribute('position',new THREE.BufferAttribute(data.positions,3));
  next.setAttribute('uv',new THREE.BufferAttribute(data.uvs,2));
  next.setIndex(data.indices);
  const colours = new Float32Array(data.count*3), colour = new THREE.Color();
  for (let i=0;i<data.count;i++) {
    const x=Math.min(source.width-1,Math.round(data.uvs[i*2]*(source.width-1)));
    const y=Math.min(source.height-1,Math.round((1-data.uvs[i*2+1])*(source.height-1)));
    const offset=(y*source.width+x)*4;
    colour.setRGB(imageData[offset]/255,imageData[offset+1]/255,imageData[offset+2]/255,THREE.SRGBColorSpace);
    colours.set([colour.r,colour.g,colour.b],i*3);
  }
  next.setAttribute('color',new THREE.BufferAttribute(colours,3));
  geometry?.dispose(); geometry=next;
  if (!mesh) {
    mesh = new THREE.Mesh(geometry,new THREE.MeshBasicMaterial({map:texture,side:THREE.DoubleSide}));
    points = new THREE.Points(new THREE.BufferGeometry(),new THREE.PointsMaterial({size:.018,vertexColors:true,sizeAttenuation:true}));
    group.add(mesh,points);
  }
  mesh.geometry=geometry;
  points.geometry.dispose(); points.geometry=new THREE.BufferGeometry();
  points.geometry.setAttribute('position',geometry.attributes.position);
  points.geometry.setAttribute('color',geometry.attributes.color);
  updatePositions();updateMode();
  ui.scene.dataset.geometryBuilds=String(++geometryBuilds);
  ui.meshStats.textContent=`${data.count.toLocaleString()} 顶点 · ${Math.round(data.indices.length/3).toLocaleString()} 三角面`;
  ui.scene.dataset.vertices=String(data.count); ui.scene.dataset.depthSource=originalFile ? (depth.ai ? 'ai' : 'pending') : 'analytic-demo';
  ui.scene.dataset.triangles=String(data.indices.length/3);
  $('saveModel').disabled=Boolean(originalFile && !depth.ai);
  $('saveDepth').disabled=Boolean(originalFile && !depth.ai);
}
function setSource(canvas, nextDepth, name, isDemo) {
  releaseSource(); source=canvas; depth=nextDepth;
  sourceURL=canvas.toDataURL('image/png');
  ui.sourceThumb.src=sourceURL; ui.originalOverlay.src=sourceURL;
  imageData=canvas.getContext('2d').getImageData(0,0,canvas.width,canvas.height).data;
  texture=new THREE.CanvasTexture(canvas); texture.colorSpace=THREE.SRGBColorSpace;
  texture.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());
  depthTexture=new THREE.CanvasTexture(depthCanvas());
  ui.sourceName.textContent=name; ui.sceneTitle.textContent=name;
  ui.sourceMeta.textContent=isDemo ? '内置几何示例 · 无需下载模型' : `${canvas.width} × ${canvas.height} · 仅保存在本机`;
  ui.sceneBadge.textContent=isDemo ? '几何示例 / DEMO' : '原图 / 待生成';
  ui.sceneInfo.textContent=isDemo ? '原创建模示例 · 上传照片后启用 AI' : '点击「生成立体影像」估计照片深度';
  resetView(); setComparison(false); rebuild();
}
function showDemo() {
  version++; originalFile=null; ui.imageInput.value='';
  const demo=createDemo(); setSource(demo.canvas,demo.depth,'空间山谷',true);
  camera.position.set(1.1,.25,distance);controls.update();
  ui.generateButton.disabled=true;
  status('先拖动示例感受空间，再放入你的照片。');
}
async function loadFile(file) {
  if (!file || busy) return;
  if (!['image/jpeg','image/png','image/webp'].includes(file.type)) return status('请选择 JPG、PNG 或 WebP 图片。',true);
  if (file.size>20*1024*1024) return status('图片超过 20 MB，请先压缩后重试。',true);
  const request=++version;
  const url=URL.createObjectURL(file);
  try {
    const image=new Image(); image.src=url; await image.decode();
    if (request!==version) return;
    if (!image.naturalWidth || !image.naturalHeight || image.naturalWidth*image.naturalHeight>80000000) throw new Error('图片尺寸过大，请缩小到 8000 万像素以内');
    const scale=Math.min(1,1600/Math.max(image.naturalWidth,image.naturalHeight));
    const canvas=document.createElement('canvas'); canvas.width=Math.max(1,Math.round(image.naturalWidth*scale)); canvas.height=Math.max(1,Math.round(image.naturalHeight*scale));
    const ctx=canvas.getContext('2d'); ctx.fillStyle='#eef1e8'; ctx.fillRect(0,0,canvas.width,canvas.height); ctx.drawImage(image,0,0,canvas.width,canvas.height);
    originalFile=file;
    const values=new Float32Array(64*64).fill(.5);
    setSource(canvas,{values,width:64,height:64},file.name,false);
    ui.generateButton.disabled=false;
    status('图片已就绪。点击生成；首次运行会下载 AI 模型（约 27–100 MB）。');
  } catch(error) { if (request===version) status(`图片无法读取：${error.message}`,true); }
  finally { URL.revokeObjectURL(url); }
}
function generate() {
  if (!source || !originalFile || busy) return;
  setBusy(true); ui.progress.removeAttribute('value'); status('正在准备 AI 深度估计…');
  ui.loadingText.textContent='正在准备 AI 模型…';
  const id=++job;
  if (!worker) worker=new Worker(new URL('./depth-worker.js?v=20260919-2',import.meta.url),{type:'module'});
  const fail=(message)=>{stopWorker();status(message,true);};
  timer=setTimeout(()=>fail('等待超过 5 分钟。可重新生成；请确认网络能访问 Hugging Face 和 jsDelivr。'),300000);
  worker.onerror=()=>fail('AI 引擎未能加载。请检查网络后重新生成，或使用最新版 Chrome / Edge。');
  worker.onmessage=({data})=>{
    if (data.id!==job) return;
    if (data.type==='error') { console.error('Depth inference:',data.message); fail('模型加载或推理失败。请检查网络或换用新版 Chrome，然后点击生成重试。');return; }
    if (data.type==='result') {
      clearTimeout(timer);
      depth={width:data.width,height:data.height,values:data.values,ai:true};
      depthTexture.dispose();depthTexture=new THREE.CanvasTexture(depthCanvas());
      rebuild();setBusy(false);resetView();
      if(!reducedMotion.matches) {camera.position.set(.7,.15,distance);controls.update();}
      ui.sceneBadge.textContent=`AI DEPTH / ${data.backend}`;
      ui.sceneInfo.textContent='AI 单视图深度重建 · 拖动探索空间';
      status(`已生成 · Depth Anything V2 · ${data.backend}。可调整深度、对比原图或导出模型。`);
    } else {
      if (data.type==='progress') ui.progress.value=data.progress || 0;
      else ui.progress.removeAttribute('value');
      status(data.message);ui.loadingText.textContent=data.message;
    }
  };
  worker.postMessage({id,image:sourceURL});
}
function setComparison(enabled) {
  ui.originalOverlay.hidden=!enabled;ui.compareButton.setAttribute('aria-pressed',String(enabled));
  ui.compareButton.textContent=enabled ? '返回立体' : '原图对比';
}
function download(blob,name) {
  const a=document.createElement('a');const url=URL.createObjectURL(blob);
  a.href=url;a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(url),30000);
}
function filename(suffix) { return (originalFile?.name.replace(/\.[^.]+$/,'') || 'spatial-valley')+suffix; }
function resize() {
  const rect=ui.viewer.getBoundingClientRect();renderer.setSize(rect.width,rect.height,false);
  camera.aspect=rect.width/rect.height;
  camera.fov = camera.aspect < 1 ? 2*Math.atan(2.65/(distance*camera.aspect))*180/Math.PI : 45;
  camera.updateProjectionMatrix();
  dirty=true;
}
function tick(t) {
  requestAnimationFrame(tick);
  if (document.hidden || !inView || !renderer) {frameTime=t;return;}
  const dt=Math.min(.05,(t-frameTime)/1000);frameTime=t;
  const oldX=group.rotation.x,oldY=group.rotation.y;
  if (ui.motionToggle.checked && !reducedMotion.matches && !busy && !interacting && t>pausedUntil) {
    group.rotation.y=THREE.MathUtils.damp(group.rotation.y,Math.sin(t*.00026)*.15,2,dt);
    group.rotation.x=THREE.MathUtils.damp(group.rotation.x,Math.cos(t*.00019)*.045,2,dt);
  } else {
    group.rotation.y=THREE.MathUtils.damp(group.rotation.y,0,3,dt);
    group.rotation.x=THREE.MathUtils.damp(group.rotation.x,0,3,dt);
  }
  if(Math.abs(group.rotation.x)<1e-5)group.rotation.x=0;
  if(Math.abs(group.rotation.y)<1e-5)group.rotation.y=0;
  controls.update();
  if(dirty || oldX!==group.rotation.x || oldY!==group.rotation.y) {renderer.render(scene,camera);dirty=false;}
}
try {
  renderer=new THREE.WebGLRenderer({canvas:ui.scene,antialias:true,alpha:true,preserveDrawingBuffer:true});
  renderer.setPixelRatio(Math.min(devicePixelRatio,2));renderer.outputColorSpace=THREE.SRGBColorSpace;
  scene=new THREE.Scene();scene.add(group);
  camera=new THREE.PerspectiveCamera(45,1,.1,100);camera.position.z=distance;
  controls=new OrbitControls(camera,ui.scene);controls.enableDamping=true;controls.enablePan=false;
  controls.minDistance=3.3;controls.maxDistance=12;controls.minAzimuthAngle=-.75;controls.maxAzimuthAngle=.75;
  controls.minPolarAngle=Math.PI/2-.5;controls.maxPolarAngle=Math.PI/2+.5;
  controls.addEventListener('start',()=>{interacting=true;});
  controls.addEventListener('end',()=>{interacting=false;pausedUntil=performance.now()+12000;});
  controls.addEventListener('change',()=>{dirty=true;});
  new IntersectionObserver(([entry])=>{inView=entry.isIntersecting;dirty=true;}).observe(ui.viewer);
  new ResizeObserver(resize).observe(ui.viewer);resize();
  if (reducedMotion.matches) ui.motionToggle.checked=false;
  showDemo();requestAnimationFrame(tick);
} catch(error) {
  console.error(error);$('renderError').hidden=false;status('当前浏览器无法启动 WebGL，请启用硬件加速。',true);
  document.querySelectorAll('button,input').forEach(el=>el.disabled=true);
}
ui.imageInput.addEventListener('change',()=>loadFile(ui.imageInput.files[0]));
for (const type of ['dragenter','dragover']) ui.dropZone.addEventListener(type,e=>{e.preventDefault();ui.dropZone.classList.add('dragging');});
for (const type of ['dragleave','drop']) ui.dropZone.addEventListener(type,e=>{e.preventDefault();ui.dropZone.classList.remove('dragging');});
ui.dropZone.addEventListener('drop',e=>loadFile(e.dataTransfer.files[0]));
window.addEventListener('dragover',e=>e.preventDefault());
window.addEventListener('drop',e=>e.preventDefault());
ui.generateButton.addEventListener('click',generate);
$('cancelButton').addEventListener('click',()=>{stopWorker();status('已取消。可重新生成，已下载的模型文件会尽可能复用。');});
$('demoButton').addEventListener('click',showDemo);
ui.depthControl.addEventListener('input',()=>{ui.depthValue.value=ui.depthControl.value+'%';schedulePositions();});
ui.detailControl.addEventListener('input',()=>{ui.detailValue.value=({'80':'轻量','160':'标准','240':'精细'})[ui.detailControl.value];rebuild();});
ui.invertToggle.addEventListener('change',()=>{depthTexture.dispose();depthTexture=new THREE.CanvasTexture(depthCanvas());updatePositions();updateMode();});
$('edgeToggle').addEventListener('change',rebuild);
document.querySelectorAll('[data-mode]').forEach(button=>button.addEventListener('click',()=>{
  mode=button.dataset.mode;document.querySelectorAll('[data-mode]').forEach(b=>b.setAttribute('aria-pressed',String(b===button)));setComparison(false);updateMode();
}));
ui.compareButton.addEventListener('click',()=>setComparison(ui.originalOverlay.hidden));
$('resetButton').addEventListener('click',()=>{
  ui.depthControl.value=45;ui.depthValue.value='45%';ui.detailControl.value=160;ui.detailValue.value='标准';ui.invertToggle.checked=false;
  $('edgeToggle').checked=false;setComparison(false);
  depthTexture.dispose();depthTexture=new THREE.CanvasTexture(depthCanvas());resetView();rebuild();
});
$('fullscreenButton').addEventListener('click',async()=>{
  try {
    if(document.fullscreenElement) await document.exitFullscreen();
    else if(ui.viewer.requestFullscreen) await ui.viewer.requestFullscreen();
    else status('此浏览器不支持元素全屏，可使用浏览器自带全屏功能。');
  } catch {status('浏览器未允许全屏，可使用浏览器自带全屏功能。');}
});
document.addEventListener('fullscreenchange',()=>{$('fullscreenButton').setAttribute('aria-label',document.fullscreenElement ? '退出全屏' : '全屏预览');});
ui.scene.addEventListener('keydown',e=>{
  if(e.key==='0'){resetView();return;}
  if(!['ArrowLeft','ArrowRight','ArrowUp','ArrowDown'].includes(e.key))return;
  e.preventDefault();ui.motionToggle.checked=false;
  const spherical=new THREE.Spherical().setFromVector3(camera.position);
  spherical.theta=THREE.MathUtils.clamp(spherical.theta+(e.key==='ArrowLeft'?-.07:e.key==='ArrowRight'?.07:0),-.75,.75);
  spherical.phi=THREE.MathUtils.clamp(spherical.phi+(e.key==='ArrowUp'?-.07:e.key==='ArrowDown'?.07:0),Math.PI/2-.5,Math.PI/2+.5);
  camera.position.setFromSpherical(spherical);controls.update();
});
ui.scene.addEventListener('webglcontextrestored',()=>{dirty=true;});
$('saveImage').addEventListener('click',()=>{
  updatePositions();
  renderer.render(scene,camera);
  const canvas=document.createElement('canvas');canvas.width=ui.scene.width;canvas.height=ui.scene.height;
  const ctx=canvas.getContext('2d');ctx.fillStyle='#142d24';ctx.fillRect(0,0,canvas.width,canvas.height);
  if (ui.originalOverlay.hidden) ctx.drawImage(ui.scene,0,0,canvas.width,canvas.height);
  else {
    const scale=Math.min(canvas.width/source.width,canvas.height/source.height);
    const w=source.width*scale,h=source.height*scale;
    ctx.drawImage(source,(canvas.width-w)/2,(canvas.height-h)/2,w,h);
  }
  canvas.toBlob(blob=>{if(blob)download(blob,filename('-3d.png'));},'image/png');
});
$('saveDepth').addEventListener('click',()=>depthCanvas().toBlob(blob=>{if(blob)download(blob,filename('-depth.png'));},'image/png'));
$('saveModel').addEventListener('click',async()=>{
  updatePositions();
  const button=$('saveModel');button.disabled=true;
  const material=new THREE.MeshBasicMaterial({map:texture,side:THREE.DoubleSide});
  const exportGeometry=geometry.clone();exportGeometry.deleteAttribute('color');exportGeometry.computeVertexNormals();
  const exportMesh=new THREE.Mesh(exportGeometry,material);exportMesh.name='Single-view depth relief';
  exportMesh.userData={source:originalFile?'Depth Anything V2':'Analytic demo',representation:'2.5D single-view relief, no reconstructed back surface'};
  try {const buffer=await new GLTFExporter().parseAsync(exportMesh,{binary:true});download(new Blob([buffer],{type:'model/gltf-binary'}),filename('-relief.glb'));status('GLB 已导出，包含纹理与深度网格，可在 Blender 等软件中打开。');}
  catch(error){console.error(error);status('导出失败，请降低网格细节后重试。',true);}
  finally{material.dispose();exportGeometry.dispose();button.disabled=false;}
});
window.addEventListener('pagehide',()=>stopWorker());
