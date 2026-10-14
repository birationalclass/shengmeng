import {STARTUP_RESOURCES} from './startup-resources.js?v=demand-1';
// Observe existing requests; never fetch, preload, or change the scene's loaders.
export class LoadingTransfer {
 constructor(resources,base){
  this.base=base;this.resources=new Map(resources.map(item=>[new URL(item.url,base).pathname,{expected:item.bytes,loaded:0,complete:false,streamed:0}]));
  this.samples=[];this.seen=new Set();this.finished=false;this.measured=false;this.requests=[];
 }
 key(url){try{const value=new URL(url,this.base);return value.origin===new URL(this.base).origin?value.pathname+(value.pathname.endsWith('/')?'index.html':''):null;}catch{return null;}}
 progress(url,received,now){
  if(this.finished)return;const key=this.key(url),item=this.resources.get(key);if(!item||item.complete)return;
  const next=Math.max(item.loaded,Math.min(item.expected,received));
  if(next>item.loaded){const bytes=next-item.loaded;this.samples.push({key,time:now,bytes,stream:true});item.streamed+=bytes;}item.loaded=next;this.measured=true;
 }
 observe(entry,now){
  if(this.finished||entry.responseStatus>=400)return;const key=this.key(entry.name),item=this.resources.get(key);if(!item)return;
  const token=entry.name+':'+entry.startTime;if(this.seen.has(token))return;this.seen.add(token);
  const body=Number(entry.decodedBodySize)||0,wire=Number(entry.transferSize)||0;
  // Failed/aborted requests do not become completed resources.
  if(!body&&!wire)return;
  this.requests.push({url:entry.name,durationMs:entry.duration||0,receiveMs:Math.max(0,(entry.responseEnd||0)-(entry.responseStart||0)),bytes:body,cached:wire===0});
  const streamed=item.complete?0:item.streamed,time=Number.isFinite(entry.responseEnd)?Math.min(now,entry.responseEnd):now;
  if(!wire)this.samples=this.samples.filter(sample=>sample.key!==key||!sample.stream);
  else if(wire>streamed)this.samples.push({key,time,bytes:wire-streamed,stream:false});
  if(!item.complete){item.expected=body||item.expected;item.loaded=item.expected;item.complete=true;}
  this.measured=true;
 }
 snapshot(now){
  this.samples=this.samples.filter(sample=>sample.time>now-2000);
  let loaded=0,total=0;for(const item of this.resources.values()){loaded+=item.loaded;total+=item.expected;}
  return {loaded,total,bytesPerSecond:this.finished?0:this.samples.reduce((sum,sample)=>sum+sample.bytes,0)/2,measured:this.measured};
 }
 finish(){this.finished=true;this.samples=[];}
}
export function formatBytes(bytes){return bytes>=1e6?(bytes/1e6).toFixed(2)+' MB':(bytes/1000).toFixed(1)+' KB';}
if(typeof document!=='undefined'){
 const world=document.getElementById('world'),background=document.getElementById('postEntryLoad');
 if(world&&background&&typeof MutationObserver!=='undefined'){
  const report=()=>{const entered=world.dataset.entered==='true',hall=world.dataset.hallPreparation,environment=world.dataset.backgroundPreparation;background.hidden=!entered||hall==='ready';background.textContent=hall==='error'?'报告厅暂未就绪':hall!=='ready'?'正在准备报告厅…':environment==='error'?'环境资源暂未完整加载':'正在完善环境…';};
  new MutationObserver(report).observe(world,{attributes:true,attributeFilter:['data-entered','data-hall-preparation','data-background-preparation']});report();
 }
 const output=document.getElementById('loadTransfer'),loading=document.getElementById('loading');
 if(output&&loading){
  const meter=new LoadingTransfer(STARTUP_RESOURCES,new URL('./',import.meta.url).href),clock=()=>performance.now(),stages=[];let observer,timer,stageObserver,stageAt=0,stageLabel='连接空间';
  const recordStage=()=>{const next=loading.dataset.ready==='true'?'加载完成':document.getElementById('loadMessage')?.textContent||stageLabel;if(next!==stageLabel){const end=clock();stages.push({stage:stageLabel,startMs:stageAt,durationMs:end-stageAt});stageAt=end;stageLabel=next;output.dataset.stageTimings=JSON.stringify(stages);}};
  const paint=()=>{const value=meter.snapshot(clock());output.textContent=`加载速度 ${value.measured?Math.round(value.bytesPerSecond/1000):'—'} KB/s · ${formatBytes(value.loaded)} / ${formatBytes(value.total)}`;output.dataset.loadedBytes=String(value.loaded);output.dataset.totalBytes=String(value.total);output.dataset.bytesPerSecond=String(value.bytesPerSecond);};
  const collect=()=>{for(const entry of [...performance.getEntriesByType('navigation'),...performance.getEntriesByType('resource')])meter.observe(entry,clock());};
  const stop=()=>{if(meter.finished)return;collect();recordStage();meter.finish();observer?.disconnect();stageObserver?.disconnect();clearInterval(timer);paint();output.dataset.loadingMs=String(clock());output.dataset.pendingFiles=JSON.stringify([...meter.resources].filter(([,item])=>!item.complete).map(([url])=>url));output.dataset.slowestResources=JSON.stringify([...meter.requests].sort((a,b)=>b.durationMs-a.durationMs).slice(0,12));};
  window.refugeTransfer={progress:(url,bytes)=>{meter.progress(url,bytes,clock());paint();},finish:stop};
  try{performance.setResourceTimingBufferSize?.(1000);collect();if(typeof PerformanceObserver!=='undefined'){observer=new PerformanceObserver(list=>{for(const entry of list.getEntries())meter.observe(entry,clock());paint();});observer.observe({type:'resource',buffered:true});}}catch{/* Keep the loading screen available on older browsers. */}
  if(typeof MutationObserver!=='undefined'){stageObserver=new MutationObserver(recordStage);stageObserver.observe(document.getElementById('loadMessage'),{childList:true,characterData:true,subtree:true});stageObserver.observe(loading,{attributes:true,attributeFilter:['data-ready']});}
  paint();timer=setInterval(()=>{collect();paint();if(loading.dataset.ready==='true'||loading.hidden)stop();},250);
 }
}
