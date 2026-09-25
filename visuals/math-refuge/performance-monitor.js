export function summarizeFrames(frames){
 if(!frames.length)return null;
 const sorted=frames.map(f=>f.ms).sort((a,b)=>a-b),cpu=frames.map(f=>f.cpu).sort((a,b)=>a-b);
 const mean=frames.reduce((sum,f)=>sum+f.ms,0)/frames.length;
 return {fps:1000/mean,mean,p95:sorted[Math.ceil(sorted.length*.95)-1],cpu:cpu[Math.ceil(cpu.length*.95)-1]};
}

// Reuse the scene's animation loop and asynchronous GPU query. No extra RAF,
// synchronous GPU reads, or monitoring work while the panel is closed.
export function createPerformanceMonitor(doc=document){
 const $=id=>doc.getElementById(id),panel=$('performancePanel'),button=$('performanceButton');
 const frames=[],history=[];let last=0,lastGPU=null,gpuAt=-Infinity;
 const write=(id,value)=>{$(id).textContent=value;};
 const reset=()=>{frames.length=0;history.length=0;last=0;$('performanceGraph').setAttribute('points','');};
 function show(value){
  panel.hidden=!value;button.setAttribute('aria-expanded',String(value));reset();
  if(value){write('performanceFPS','—');write('performanceStatus','正在采样…');}
 }
 button.addEventListener('click',()=>show(panel.hidden));
 $('performanceClose').addEventListener('click',()=>{show(false);button.focus();});
 doc.addEventListener('keydown',event=>{if(event.key==='Escape'&&!panel.hidden){show(false);button.focus();}});
 doc.addEventListener('visibilitychange',()=>{reset();lastGPU=null;if(!panel.hidden){write('performanceFPS','—');write('performanceStatus',doc.hidden?'页面在后台 · 监测暂停':'正在采样…');}});
 const ms=value=>Number.isFinite(value)?value.toFixed(1)+' ms':'—';
 return {
  get visible(){return !panel.hidden;},
  gpu(value,stamp){if(Number.isFinite(value)){lastGPU=value;gpuAt=stamp;}},
  frame(stamp,frameMs,cpuMs,renderer,{gpuSupported=false,ratio=1,rooms=0,adaptive='自动监测'}={}){
   if(panel.hidden||doc.hidden||!Number.isFinite(frameMs)||frameMs<=0)return;
   frames.push({ms:frameMs,cpu:cpuMs});if(frames.length>240)frames.shift();
   // A rolling two-second sample includes long frames, rather than hiding stalls.
   let span=frames.reduce((sum,f)=>sum+f.ms,0);
   while(frames.length>1&&span-frames[0].ms>=2000)span-=frames.shift().ms;
   if(stamp-last<500)return;last=stamp;
   const stats=summarizeFrames(frames),info=renderer.info,canvas=renderer.domElement;
   write('performanceFPS',stats.fps.toFixed(0));write('performanceStatus','最近约 2 秒 · 每 0.5 秒更新');
   write('performanceFrame',ms(stats.mean));write('performanceP95',ms(stats.p95));write('performanceCPU',ms(stats.cpu));
   write('performanceGPU',!gpuSupported?'浏览器不支持':lastGPU!==null&&stamp-gpuAt<2500?ms(lastGPU):'等待采样');
   write('performanceCalls',info.render.calls.toLocaleString());write('performanceTriangles',info.render.triangles.toLocaleString());
   write('performanceTextures',info.memory.textures.toLocaleString());write('performanceGeometries',info.memory.geometries.toLocaleString());
   write('performanceResolution',canvas.width+' × '+canvas.height);write('performanceScale',ratio.toFixed(2)+'×');write('performanceRooms',String(rooms));write('performanceAdaptive',adaptive);
   history.push(stats.fps);if(history.length>60)history.shift();
   const max=Math.max(60,...history);
   $('performanceGraph').setAttribute('points',history.map((v,i)=>(i*280/59).toFixed(1)+','+(44-Math.min(1,v/max)*40).toFixed(1)).join(' '));
   write('performanceGraphScale',Math.ceil(max)+' FPS');
  }
 };
}
