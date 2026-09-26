import {OceanRenderer} from './ocean-renderer.js?v=optical-budget-2';
import {Color} from '../3d/vendor/three.module.js';
import {createGpuTimer} from '../math-refuge/render-budget.js';
import {presets,percentile,resourceScore,bufferBytes} from './optical-budget.js';
const $=id=>document.getElementById(id),canvas=$('sea');
const state={wave:1.2,wind:.45,sun:5,time:7.1,yaw:0,pitch:0,distance:0,quality:'balanced',scale:1};
let active=true,paused=matchMedia('(prefers-reduced-motion: reduce)').matches,last=0,pointer=null,engine,timer;
let preset=innerWidth<700?'eco':'balanced',optics=true,dirty=true,epoch=0,samples=[],gpuSamples=[],results={},benchmark=null,bytes=0;
let nextDraw=0,comparisonLocked=false;
const descriptions={eco:'30 帧上限 · 65 万像素 · 保留立体白浪与湿沙，适合长时间运行。',balanced:'60 帧上限 · 95 万像素 · 中等网格、7 层细波，推荐日常观察。',fine:'60 帧上限 · 150 万像素 · 完整网格、9 层细波，适合近距离比较。'};
// These enhancements are local to experiment 02. Other ocean studies and the
// campus continue to use their original shader and material configuration.
function enhance(){
  const m=engine.water.material;
  m.fragmentShader=m.fragmentShader.replace('for(int i=0;i<9;i++)','for(int i=0;i<DETAIL_BANDS;i++)');
  m.fragmentShader=m.fragmentShader.replace('vec2 dir=vec2(cos(band*2.399+.3),sin(band*2.399+.3));',
    'float heading=.45+sin(band*2.399)*.68;vec2 dir=vec2(cos(heading),sin(heading));');
  m.fragmentShader=m.fragmentShader.replace('noise(uv*.42+band*7.1)',
    'noise(uv*.42-vec2(uTime*.09,uTime*.025)+band*7.1)');
  m.fragmentShader=m.fragmentShader.replace('(.035+.065*uWind)', '(.021+.042*uWind)');
  m.fragmentShader=m.fragmentShader.replace('body=transmittedWater(vWorld,view,n);',`body=transmittedWater(vWorld,view,n);
    // A thin, back-lit crest transmits more light than the deep water below.
    float crestPath=max(.02,waterThickness)/max(.25,abs(dot(n,sd)));
    float crestLight=pow(max(0.,dot(-view,sd)),4.)*smoothstep(.08,.55,vWorld.y)*exp(-crestPath*1.8);
    body+=vec3(.025,.15,.12)*crestLight*(1.-dusk)*smoothstep(-2.,6.,uSun);`);
  // 3 evaluations instead of 5, with a small forward difference. Full central
  // differences remain available in the fine preset for direct comparison.
  m.vertexShader=m.vertexShader.replace('vec3 dc=surfaceAt(ca+vec2(.035,0.))-surfaceAt(ca-vec2(.035,0.));vec3 da=surfaceAt(ca+vec2(0.,.08))-surfaceAt(ca-vec2(0.,.08));',`
    #ifdef ECONOMY_NORMALS
    vec3 dc=surfaceAt(ca+vec2(.0175,0.))-p;vec3 da=surfaceAt(ca+vec2(0.,.04))-p;
    #else
    vec3 dc=surfaceAt(ca+vec2(.035,0.))-surfaceAt(ca-vec2(.035,0.));vec3 da=surfaceAt(ca+vec2(0.,.08))-surfaceAt(ca-vec2(0.,.08));
    #endif
  `);
}
function setDefines(){
  for(const mesh of [engine.water,engine.beach]){
    mesh.material.defines={...(optics?{COASTAL_OPTICS:1}:{}),DETAIL_BANDS:presets[preset].bands,...(preset!=='fine'?{ECONOMY_NORMALS:1}:{})};
    mesh.material.needsUpdate=true;
  }
}
function resetSamples(){samples=[];gpuSamples=[];epoch=performance.now();timer?.dispose();timer=createGpuTimer(engine.renderer.getContext());}
function restartFoam(){
  const renderer=engine.renderer,color=renderer.getClearColor(new Color()),alpha=renderer.getClearAlpha(),target=renderer.getRenderTarget();
  try{renderer.setClearColor(0,0);for(const buffer of [engine.foamA,engine.foamB]){renderer.setRenderTarget(buffer);renderer.clear();}}
  finally{renderer.setRenderTarget(target);renderer.setClearColor(color,alpha);}
  engine.lastTime=null;engine.foamAccumulator=0;
}
function resize(){
  const ratio=Math.min(devicePixelRatio,Math.sqrt(presets[preset].pixels/(innerWidth*innerHeight)));
  engine.resize(Math.max(1,Math.round(innerWidth*ratio)),Math.max(1,Math.round(innerHeight*ratio)));dirty=true;resetSamples();
}
function applyPreset(key){
  preset=key;$('quality').value=key;state.quality=presets[key].quality;
  for(const o of engine.scene.children)if(o.isPoints)o.geometry.setDrawRange(0,Math.floor(o.geometry.attributes.position.count*presets[key].particles));
  setDefines();resize();last=0;$('budget-note').textContent=descriptions[key];
  renderTable();
}
function mode(value){optics=value;setDefines();$('new').setAttribute('aria-pressed',String(value));$('old').setAttribute('aria-pressed',String(!value));invalidate();}
function invalidate(){results={};comparisonLocked=false;resetSamples();dirty=true;renderTable();}
function renderTable(){
  $('comparison').innerHTML=Object.entries(presets).map(([key,p])=>{
    const r=results[key];return `<tr data-active="${key===preset}"><th>${p.name}</th><td>${r?r.fps.toFixed(0):'—'}</td><td>${r?r.cpu.toFixed(1):'—'}</td><td>${r?.gpu!=null?r.gpu.toFixed(1):'—'}</td><td>${r?r.memory.toFixed(1):'—'}</td><td>${r?r.score:'—'}</td></tr>`;
  }).join('');
}
function draw(now){
  const gpu=timer.poll(now);if(gpu!=null&&now-epoch>1200)gpuSamples.push(gpu);
  engine.renderer.info.reset();timer.begin(now);const start=performance.now();
  try{engine.draw(state);}finally{timer.end();}
  const cpu=performance.now()-start,info=engine.renderer.info.render;
  if(now-epoch>1200)samples.push({now,cpu,triangles:info.triangles,calls:info.calls,points:info.points});
  if(!benchmark){samples=samples.filter(s=>now-s.now<4000);if(gpuSamples.length>20)gpuSamples.shift();}
  canvas.dataset.time=state.time.toFixed(3);canvas.dataset.preset=preset;
}
function summarize(){
  if(samples.length<10)return null;
  const elapsed=samples.at(-1).now-samples[0].now;if(elapsed<500)return null;
  const fps=(samples.length-1)*1000/elapsed,cpu=percentile(samples.map(s=>s.cpu)),gpu=percentile(gpuSamples);
  const triangles=Math.max(...samples.map(s=>s.triangles)),pixels=canvas.width*canvas.height;
  const memory=(bufferBytes(engine.scene)+2*engine.foamA.width*engine.foamA.height*8+512*160*8)/1048576;
  return {fps,cpu,gpu,triangles,pixels,memory,score:resourceScore({fps,cpu,gpu,pixels,triangles,target:presets[preset].fps})};
}
function report(){
  bytes=bufferBytes(engine.scene);
  const r=summarize();$('fps').textContent=paused?'暂停':r?r.fps.toFixed(0):'…';$('cpu').textContent=r?r.cpu.toFixed(1):'…';$('gpu').textContent=r?.gpu!=null?r.gpu.toFixed(1):'—';
  $('score').textContent=paused?'已暂停':r?`${r.score} / 100`:'采样中';
  const heap=performance.memory?.usedJSHeapSize;
  // Typed buffers + known texture storage only: excludes driver, programs,
  // default framebuffer, MSAA and browser overhead. Not total VRAM usage.
  const textures=2*engine.foamA.width*engine.foamA.height*8+512*160*8;
  const s=samples.at(-1);
  $('resources').textContent=`${canvas.width} × ${canvas.height} · ${s?(s.triangles/10000).toFixed(1):'—'} 万三角形/帧 · ${s?(s.points/1000).toFixed(1):'—'} 千粒子 · ${s?.calls??'—'} 次绘制`;
  $('memory').textContent=`几何缓冲 ${(bytes/1048576).toFixed(1)} MiB + 浪沫/剖面纹理 ${(textures/1048576).toFixed(1)} MiB（估算）${heap?` · JS 堆 ${(heap/1048576).toFixed(0)} MiB（浏览器口径）`:''}`;
  if(r&&!benchmark&&!paused&&!comparisonLocked){results[preset]=r;renderTable();}
  $('status').textContent=benchmark?`对比采样 · ${presets[preset].name}`:`${paused?'已暂停':presets[preset].fps+' 帧上限'} · ${optics?'改良水材质':'原版材质对照'}`;
}
function endBenchmark(cancel=false){
  if(!benchmark)return;const saved=benchmark.saved;benchmark=null;comparisonLocked=!cancel;
  Object.assign(state,saved.state);paused=saved.paused;optics=saved.optics;applyPreset(saved.preset);
  $('light').value=String(state.sun);$('wave').value=String(state.wave);$('height').value=state.wave.toFixed(1)+' m';
  restartFoam();
  $('new').setAttribute('aria-pressed',String(optics));$('old').setAttribute('aria-pressed',String(!optics));
  $('pause').textContent=paused?'继续':'暂停';
  for(const e of document.querySelectorAll('section button,section select,section input'))e.disabled=false;
  $('benchmark').textContent='同场景比较 · 约 18 秒';$('benchmark').disabled=false;
  $('measurement-note').textContent=cancel?'比较已中止；切换回来可重新测量。':'同场景结果已保留；改变光照、浪高或视角后重新采样。';renderTable();
}
function benchmarkNext(){
  const key=benchmark.queue.shift();if(!key){endBenchmark();return;}
  Object.assign(state,{wave:1.2,wind:.45,sun:24,time:7.1,yaw:0,pitch:0,distance:0});optics=true;paused=false;
  $('light').value='24';$('wave').value='1.2';$('height').value='1.2 m';
  $('new').setAttribute('aria-pressed','true');$('old').setAttribute('aria-pressed','false');
  applyPreset(key);restartFoam();benchmark.started=0;
}
function startBenchmark(){
  results={};benchmark={saved:{state:{...state},preset,paused,optics},queue:Object.keys(presets),started:0};
  for(const e of document.querySelectorAll('section button,section select,section input'))e.disabled=true;
  $('benchmark').textContent='取消比较';$('measurement-note').textContent='固定晴日、浪高与视角；每档先预热，再采样约 4 秒。';benchmarkNext();
}
let reportAt=0;
function tick(now){
  if(active&&!document.hidden){
    const interval=1000/presets[preset].fps,due=!last||now>=nextDraw-.6;
    if(dirty||(!paused&&due)){
      if(!paused&&last)state.time+=Math.min(.1,(now-last)/1000);
      draw(now);last=now;dirty=false;
      nextDraw=now+interval-(nextDraw&&now-nextDraw<interval*2?Math.max(0,now-nextDraw)%interval:0);
      // Compilation and initial foam warm-up are excluded from measurements.
      if(benchmark&&!benchmark.started){benchmark.started=performance.now();resetSamples();}
    }
    if(now-reportAt>700){report();reportAt=now;}
    if(benchmark&&now-benchmark.started>5700){const r=summarize();if(r)results[preset]=r;benchmarkNext();}
  }else last=0;
  requestAnimationFrame(tick);
}
try{
  engine=new OceanRenderer(canvas,{opticalStudy:true});engine.renderer.info.autoReset=false;enhance();applyPreset(preset);
  if(innerWidth<700)$('resource-panel').open=false;
  $('quality').onchange=e=>applyPreset(e.target.value);$('benchmark').onclick=()=>benchmark?endBenchmark(true):startBenchmark();
  $('new').onclick=()=>mode(true);$('old').onclick=()=>mode(false);
  $('light').onchange=e=>{state.sun=+e.target.value;invalidate();};
  $('wave').oninput=e=>{state.wave=+e.target.value;$('height').value=state.wave.toFixed(1)+' m';invalidate();};
  $('pause').textContent=paused?'继续':'暂停';$('pause').onclick=()=>{paused=!paused;$('pause').textContent=paused?'继续':'暂停';last=0;resetSamples();};
  $('reset').onclick=()=>{state.yaw=state.pitch=state.distance=0;invalidate();};
  canvas.onpointerdown=e=>{if(benchmark)return;pointer={id:e.pointerId,x:e.clientX,y:e.clientY};canvas.setPointerCapture(e.pointerId);};
  canvas.onpointermove=e=>{if(!pointer||pointer.id!==e.pointerId)return;state.yaw=Math.max(-.65,Math.min(.65,state.yaw-(e.clientX-pointer.x)*.0018));state.pitch=Math.max(-.12,Math.min(.22,state.pitch+(e.clientY-pointer.y)*.0011));pointer.x=e.clientX;pointer.y=e.clientY;invalidate();};
  canvas.onpointerup=canvas.onpointercancel=()=>pointer=null;
  canvas.addEventListener('wheel',e=>{e.preventDefault();if(benchmark)return;state.distance=Math.max(-1.2,Math.min(5,state.distance+e.deltaY*.005));invalidate();},{passive:false});
  addEventListener('resize',()=>{endBenchmark(true);results={};resize();renderTable();});
  addEventListener('message',e=>{if(e.origin===location.origin&&e.source===parent&&e.data?.type==='ocean-experiment-visibility'){active=!!e.data.active;if(!active)endBenchmark(true);last=0;resetSamples();}});
  document.addEventListener('visibilitychange',()=>{if(document.hidden)endBenchmark(true);last=0;resetSamples();});
  requestAnimationFrame(tick);
}catch(e){$('status').textContent='无法启动：'+e.message;console.error(e);}
