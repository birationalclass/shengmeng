export const bytesText=bytes=>bytes==null?'大小待确认':bytes>=1e6?(bytes/1e6).toFixed(2)+' MB':(bytes/1000).toFixed(1)+' KB';
export class RuntimeTransfers {
 constructor(base){this.base=base;this.active=new Map();this.samples=[];this.seen=new Set();this.total=0;this.last=null;this.serial=0;}
 name(url){try{const u=new URL(url,this.base);return decodeURIComponent(u.pathname.split('/').filter(Boolean).slice(-2).join('/'));}catch{return '资源';}}
 begin(url,total,now){const id=++this.serial;this.active.set(id,{id,url,name:this.name(url),received:0,total,start:now});return id;}
 progress(id,bytes,now){const item=this.active.get(id);if(!item)return;const delta=Math.max(0,bytes-item.received);item.received=bytes;if(delta)this.samples.push({url:item.url,time:now,bytes:delta,stream:true});}
 end(id,error=false){const item=this.active.get(id);if(!item)return;this.active.delete(id);this.last={...item,error,complete:!error};}
 observe(entry,now){const token=entry.name+':'+entry.startTime;if(this.seen.has(token))return;this.seen.add(token);if(entry.responseStatus>=400)return;
   const body=Number(entry.decodedBodySize)||0,wire=Number(entry.transferSize)||0;if(!body&&!wire)return;
   const streamed=this.samples.filter(s=>s.url===entry.name&&s.stream&&s.time>=entry.startTime),count=streamed.reduce((sum,s)=>sum+s.bytes,0);
   this.samples=this.samples.filter(s=>!streamed.includes(s));
   // ResourceTiming corrects cache reads and compressed transfers after completion.
   if(wire)this.samples.push({url:entry.name,time:entry.responseEnd??now,bytes:wire,stream:false});this.total+=body;
   if(!this.active.size)this.last={url:entry.name,name:this.name(entry.name),received:body,total:body,complete:true,cached:wire===0};
 }
 snapshot(now){this.samples=this.samples.filter(s=>s.time>now-2000);return {active:[...this.active.values()],last:this.last,total:this.total,speed:this.samples.reduce((s,v)=>s+v.bytes,0)/2};}
}
export const runtimeTransfers=typeof location==='undefined'?null:new RuntimeTransfers(location.href);
let scheduler=null,manual=null;
export function loadingContent(label){manual=label;}
export function connectLoadingScheduler(value){scheduler=value;}
export function loadingState(now=performance.now()){
 const s=scheduler?.snapshot();return {...runtimeTransfers?.snapshot(now),pauseReason:s?.pauseReason||'',content:s?.active?s.content:manual||s?.error||s?.content||'开场资源准备中'};
}
// One streaming pass, without cloning/buffering a second response. Modules/images/audio
// loaded by the browser are reported by ResourceTiming when their requests complete.
if(typeof window!=='undefined'){
 const nativeFetch=window.fetch.bind(window),now=()=>performance.now();
 window.fetch=async function(input,options){const url=new URL(typeof input==='string'||input instanceof URL?input:input.url,location.href).href,id=runtimeTransfers.begin(url,null,now());
   try{const response=await nativeFetch(input,options);const item=runtimeTransfers.active.get(id),length=Number(response.headers.get('content-length'));if(item)item.total=length>0&&!response.headers.get('content-encoding')?length:null;
     if(!response.body||!response.ok){runtimeTransfers.end(id,!response.ok);return response;}
     const reader=response.body.getReader();let received=0;const stream=new ReadableStream({async pull(controller){try{const {value,done}=await reader.read();if(done){runtimeTransfers.end(id);controller.close();reader.releaseLock();return;}received+=value.byteLength;runtimeTransfers.progress(id,received,now());controller.enqueue(value);}catch(error){runtimeTransfers.end(id,true);controller.error(error);}},cancel(reason){runtimeTransfers.end(id,true);return reader.cancel(reason);}});
     const observed=new Response(stream,{status:response.status,statusText:response.statusText,headers:response.headers});Object.defineProperties(observed,{url:{value:response.url},redirected:{value:response.redirected},type:{value:response.type}});return observed;
   }catch(error){runtimeTransfers.end(id,true);throw error;}
 };
 try{performance.setResourceTimingBufferSize?.(2000);new PerformanceObserver(list=>{for(const entry of list.getEntries())runtimeTransfers.observe(entry,now());}).observe({type:'resource',buffered:true});}catch{}
 const paint=()=>{const out=document.getElementById('runtimeLoad'),world=document.getElementById('world');if(!out)return;const t=runtimeTransfers.snapshot(now()),s=scheduler?.snapshot(),item=t.active[0]||t.last,entered=world?.dataset.entered==='true';out.hidden=!entered;out.dataset.loading=String(entered&&Boolean(t.active.length||s?.active));
   const nav=document.getElementById('chapters'),navigation=nav&&!nav.hidden?nav.getBoundingClientRect():null;out.style.bottom=Math.max(16,navigation?.height?innerHeight-navigation.top+8:16)+'px';
   const content=(s?.active?s.content:manual||s?.error||s?.content||'空闲 · 按需准备')+(s?.pauseReason?'（等待：'+s.pauseReason+'）':'');
   const load=s?.frameMs?`帧 ${s.frameMs.toFixed(1)} / ${s.frameBudget.toFixed(1)} ms · 加载 ${s.cpuMs.toFixed(1)} ms/批`:'负荷采样中';
   const download=item?`${item.name}${item.complete?'（'+(item.cached?'缓存':'完成')+'）':item.error?'（失败）':'（下载中）'} ${bytesText(item.received)}${item.total!=null&&!item.complete?' / '+bytesText(item.total):''}`:'无下载';
   out.textContent=`加载：${s?.protected?(world?.dataset.openingGPU==='ready'?'开场保护 · '+(s.pending?'按需任务等待':'P0/P1 已就绪'):'开场准备 · '+content):content} · 负荷：${load}\n下载：${download}${t.active.length>1?' · 另 '+(t.active.length-1)+' 项':''} · ${Math.round(t.speed/1000)} KB/s · 已接收 ${bytesText(t.total)}${world?.dataset.cloudPreparation==='ready'?' · 云：'+world.dataset.cloudReason:''}`;
   out.dataset.content=content;out.dataset.pauseReason=s?.pauseReason||'';out.dataset.pending=String(s?.pending||0);out.dataset.protected=String(s?.protected||false);out.dataset.frameMs=String(s?.frameMs||0);out.dataset.loadingCpuMs=String(s?.cpuMs||0);out.dataset.activeDownloads=String(t.active.length);out.dataset.receivedBytes=String(t.total);out.dataset.speed=String(t.speed);
 };setInterval(paint,500);
}
