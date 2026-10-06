// Page-local diagnostics: these are browser measurements, never machine CPU/GPU estimates.
const state={renders:[],gaps:[],layouts:[],longTasks:[],lastRender:0,lastFrame:0,renderCount:0,visibleNodes:0,totalNodes:0,visibleLinks:0,totalLinks:0,dom:0};
let hud=null,timer=0,observer=null,lastDOM=-Infinity;
const keep=(array,value,limit=120)=>{array.push(value);if(array.length>limit)array.shift();};
const average=xs=>xs.length?xs.reduce((a,b)=>a+b,0)/xs.length:0;
export function recordAtlasRender(start,counts,frameTime){
 const now=performance.now();keep(state.renders,now-start);
 const gap=frameTime-state.lastFrame;if(gap>5&&gap<250)keep(state.gaps,gap,60);
 if(gap>=250)state.gaps=[];state.lastRender=now;state.lastFrame=frameTime;state.renderCount++;Object.assign(state,counts);
}
export function recordAtlasLayout(start){keep(state.layouts,performance.now()-start,30);}
export function atlasPerformanceSnapshot(){
 const now=performance.now();state.longTasks=state.longTasks.filter(e=>now-e.time<30000);
 const memory=performance.memory;
 return {mode:'2d',idle:now-state.lastRender>1000,fps:state.gaps.length?Math.min(240,Math.round(1000/average(state.gaps))):null,
  renderMs:average(state.renders),layoutMs:average(state.layouts),longTasks:state.longTasks.length,
  longTaskMs:state.longTasks.reduce((s,e)=>s+e.duration,0),heapUsed:memory?.usedJSHeapSize??null,
  heapLimit:memory?.jsHeapSizeLimit??null,renderCount:state.renderCount,visibleNodes:state.visibleNodes,totalNodes:state.totalNodes,
  visibleLinks:state.visibleLinks,totalLinks:state.totalLinks,dom:state.dom,cpuPercent:null,gpuPercent:null};
}
function update(){
 if(document.hidden||!hud)return;
 const now=performance.now();if(now-lastDOM>5000){state.dom=document.getElementsByTagName('*').length;lastDOM=now;}
 const p=atlasPerformanceSnapshot(),en=document.documentElement.lang.startsWith('en');
 const MB=n=>(n/1048576).toFixed(0);
 const frame=p.idle?(en?'idle':'静止'):p.fps===null?'FPS —':p.fps+' FPS';
 hud.firstElementChild.textContent=`2D · ${frame} · JS ${p.renderMs.toFixed(1)} ms · ${en?'heap':'堆'} ${p.heapUsed===null?'—':MB(p.heapUsed)+' MB'}`;
 hud.lastElementChild.textContent=`${en?'nodes':'节点'} ${p.visibleNodes}/${p.totalNodes} · ${en?'links':'线'} ${p.visibleLinks}/${p.totalLinks} · DOM ${p.dom} · ${en?'long':'长任务'} ${p.longTasks}/30s`;
 hud.title=en?`Graph render time is JavaScript work, not CPU utilization. Layout ${p.layoutMs.toFixed(1)} ms; long tasks ${p.longTaskMs.toFixed(0)} ms/30s. JS heap limit ${p.heapLimit?MB(p.heapLimit)+' MB':'unavailable'}. CPU/GPU utilization is unavailable in browsers. FPS samples graph renders during interaction. Idle sampling: once per second; DOM count: every five seconds.`:
  `JS 为图谱绘制代码耗时，不是整机 CPU 占用。布局 ${p.layoutMs.toFixed(1)} ms；长任务 ${p.longTaskMs.toFixed(0)} ms/30s。JS 堆上限 ${p.heapLimit?MB(p.heapLimit)+' MB':'不可读取'}。浏览器无法读取 CPU/GPU 占用率。FPS 采样交互时的图谱绘制；静止时每秒更新一次，DOM 每五秒计数。`;
 hud.setAttribute('aria-label',en?'Page performance diagnostics':'页面性能数据');
}
export function installPerformanceHUD(){
 if(hud)return;
 hud=document.createElement('output');hud.id='performanceHUD';hud.className='performance-hud';hud.setAttribute('aria-live','off');
 hud.append(document.createElement('span'),document.createElement('span'));document.body.append(hud);
 const footer=document.querySelector('.atlas-statusbar');
 const footerSize=footer?new ResizeObserver(()=>document.documentElement.style.setProperty('--atlas-footer-height',footer.getBoundingClientRect().height+'px')):null;
 if(footer)footerSize.observe(footer);
 if(globalThis.PerformanceObserver?.supportedEntryTypes.includes('longtask')){
  observer=new PerformanceObserver(list=>list.getEntries().forEach(e=>{keep(state.longTasks,{time:e.startTime,duration:e.duration},100);}));
  observer.observe({type:'longtask',buffered:false});
 }
 const resume=()=>{clearInterval(timer);timer=0;if(!document.hidden){update();timer=setInterval(update,1000);}};
 document.addEventListener('visibilitychange',resume);window.addEventListener('languagechange',update);
 window.addEventListener('pagehide',()=>{clearInterval(timer);observer?.disconnect();footerSize?.disconnect();},{once:true});
 resume();
 // Read-only diagnostics for reproducible browser profiling.
 window.atlasPerformance=Object.freeze({snapshot:atlasPerformanceSnapshot});
}
