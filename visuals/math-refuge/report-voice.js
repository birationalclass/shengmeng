// On-demand narration: no network or audio allocation until a report is selected.
export function createReportVoice({fetcher=globalThis.fetch,makeAudio=()=>new Audio(),makeURL=b=>URL.createObjectURL(b),revokeURL=u=>URL.revokeObjectURL(u),onChange=()=>{},baseURL=new URL('.',import.meta.url).href}={}){
 let epoch=0,attachToken=0,playToken=0,report=null,manifest=null,audio=null,desired=false,controllers=new Set(),cache=new Map(),jobs=new Map(),index=0,offset=0;
 const state={report:null,phase:'idle',progress:null,time:0,duration:0,error:'',started:false,chapter:0};
 const emit=()=>onChange({...state});
 const sync=()=>{if(audio&&manifest)state.time=Math.min(state.duration,manifest.chapters[index].start+audio.currentTime);return state.time;};
 function pause(){desired=false;playToken++;sync();audio?.pause();if(['playing','buffering','preparing'].includes(state.phase)){state.phase='paused';emit();}}
 function release(){pause();audio=null;controllers.forEach(c=>c.abort());controllers.clear();for(const v of cache.values())revokeURL(v);cache.clear();jobs.clear();}
 async function bytes(src,mine,show,sizeHint=0){
  const controller=new AbortController();controllers.add(controller);
  try{
   const response=await fetcher(src,{signal:controller.signal,cache:"no-cache"});if(!response.ok)throw Error('语音下载失败');
   const size=Number(response.headers.get('content-length'))||sizeHint,parts=[];let received=0;
   if(response.body?.getReader){const reader=response.body.getReader();for(;;){const {value,done}=await reader.read();if(done)break;if(mine!==epoch){await reader.cancel();return null;}parts.push(value);received+=value.byteLength;if(show){state.progress=size?Math.min(.99,received/size):null;emit();}}}
   else parts.push(await response.arrayBuffer());
   if(mine!==epoch)return null;return new Blob(parts,{type:'audio/mpeg'});
  }finally{controllers.delete(controller);}
 }
 function trim(){for(const [key,url] of cache)if(Math.abs(key-index)>1){revokeURL(url);cache.delete(key);}}
 async function load(i,show=true){
  if(cache.has(i))return cache.get(i);if(jobs.has(i))return jobs.get(i);
  const mine=epoch,c=manifest.chapters[i];
  const job=(async()=>{const blob=await bytes(c.src,mine,show,c.bytes);if(!blob||mine!==epoch)return null;const url=makeURL(blob);cache.set(i,url);trim();return url;})();
  jobs.set(i,job);try{return await job;}finally{if(jobs.get(i)===job)jobs.delete(i);}
 }
 async function attach(i,at=0){
  const mine=epoch,attachment=++attachToken;index=i;offset=at;audio?.pause();audio=null;
  state.chapter=i;state.time=manifest.chapters[i].start+at;
  if(!cache.has(i)){state.phase='loading';state.progress=null;emit();}
  const url=await load(i);if(!url||mine!==epoch||attachment!==attachToken)return false;
  const target=makeAudio();audio=target;target.preload='auto';target.src=url;
  const valid=()=>mine===epoch&&audio===target;
  const position=()=>{if(valid()&&at){target.currentTime=at;}};
  target.addEventListener('loadedmetadata',position,{once:true});try{position();}catch{}
  target.addEventListener('timeupdate',()=>{if(valid()){sync();emit();}});
  target.addEventListener('waiting',()=>{if(valid()&&desired){state.phase='buffering';emit();}});
  target.addEventListener('playing',()=>{if(valid()&&desired){state.phase='playing';emit();}});
  target.addEventListener('error',()=>{if(valid()){desired=false;state.phase='error';state.error='语音未就绪 · 点击重试';emit();}});
  target.addEventListener('ended',()=>{if(!valid())return;state.time=manifest.chapters[i].start+manifest.chapters[i].duration;if(i+1<manifest.chapters.length){void advance(i+1);}else{desired=false;state.phase='ended';state.time=state.duration;emit();}});
  state.progress=1;state.phase=state.started?'paused':'ready';state.error='';emit();return true;
 }
 async function play(){
  if(!audio)return false;const mine=epoch,token=++playToken,target=audio;desired=true;state.started=true;
  try{await target.play();if(mine!==epoch||token!==playToken||!desired||audio!==target){target.pause();return false;}state.phase='playing';state.error='';emit();return true;}
  catch{if(mine!==epoch||token!==playToken)return false;desired=false;state.phase='paused';state.error='点击黑板播放语音';emit();return false;}
 }
 async function advance(i){const resume=desired,mine=epoch;try{if(await attach(i)&&mine===epoch&&resume&&desired)await play();}catch(error){if(mine===epoch){desired=false;state.phase='error';state.error='语音下载失败 · 点击重试';emit();}}}
 async function select(next){
  ++epoch;++attachToken;release();report=next;manifest=null;index=0;offset=0;const mine=epoch;
  Object.assign(state,{report:next?.id,phase:next?.narration?'loading':'idle',progress:null,time:0,duration:0,error:'',started:false,chapter:0});emit();
  if(!next?.narration)return false;
  try{
   const src=new URL(next.narration.manifest,baseURL).href,controller=new AbortController();controllers.add(controller);
   let response;try{response=await fetcher(src,{signal:controller.signal,cache:"no-cache"});}finally{controllers.delete(controller);}
   if(!response.ok)throw Error('语音目录下载失败');const data=await response.json();if(mine!==epoch)return false;
   if(!data.chapters?.length||!data.boards?.length||!Number.isFinite(data.duration))throw Error('语音目录无效');
   manifest={...data,chapters:data.chapters.map(c=>({...c,src:new URL(c.src,src).href}))};state.duration=data.duration;
   return await attach(0);
  }catch(error){if(mine!==epoch||error.name==='AbortError')return false;state.phase='error';state.error='语音未就绪 · 点击重试';emit();return false;}
 }
 async function seek(time){
  if(!manifest)return false;pause();const mine=epoch,target=Math.max(0,Math.min(manifest.duration,Number(time)||0));state.started=true;
  const i=Math.max(0,manifest.chapters.findLastIndex(c=>c.start<=target)),at=Math.min(manifest.chapters[i].duration-.025,target-manifest.chapters[i].start);
  try{if(audio&&i===index){audio.currentTime=Math.max(0,at);state.time=target;state.phase='paused';emit();return true;}return await attach(i,Math.max(0,at));}
  catch{if(mine===epoch){state.phase='error';state.error='语音定位失败 · 点击重试';emit();}return false;}
 }
 async function toggle(){
  if(state.phase==='playing'||state.phase==='buffering'||state.phase==='preparing'){pause();return true;}
  if(state.phase==='loading')return false;
  if(state.phase==='error'){if(!manifest)return select(report);try{return await attach(index,offset)&&await play();}catch{return false;}}
  if(state.phase==='ended')await seek(0);
  return play();
 }
 return{state,select,toggle,pause,seek,
  async suspendUntil(job){
   if(!desired||state.phase==='preparing')return;
   const mine=epoch,token=++playToken;sync();audio?.pause();state.phase='preparing';state.progress=null;emit();
   try{await job;if(mine===epoch&&token===playToken&&desired)await play();}
   catch{if(mine===epoch&&token===playToken&&desired){pause();state.phase='error';state.error='板书尚未就绪 · 点击重试';emit();}}
  },get manifest(){return manifest;},
  update(){sync();if(manifest&&desired&&audio&&index+1<manifest.chapters.length&&manifest.chapters[index].duration-audio.currentTime<20){void load(index+1,false).catch(()=>{});}return state;},
  dispose(){++epoch;release();manifest=null;state.phase='idle';emit();}};
}
// Use the same measured stroke costs as chalkPosition and inkReveal, so a
// long formula is never treated as one equal-sized slice of a whole board.
const lineCostBounds=new WeakMap();
export function rowNarrationProgress(cues,time,plan){
 if(!cues?.length||!plan?.total)return null;
 let bounds=lineCostBounds.get(plan);if(!bounds){bounds=new Map();
 for(const s of plan.segments){if(!Number.isInteger(s.mainLine))continue;const b=bounds.get(s.mainLine);if(b)b.end=s.end;else bounds.set(s.mainLine,{start:s.start,end:s.end});}
 lineCostBounds.set(plan,bounds);}
 let completed=0;
 for(const cue of cues){
  const b=bounds.get(cue.row);if(!b)throw Error('Narration row has no visible ink: '+cue.row);
  if(time<cue.writeStart)return completed/plan.total;
  if(time<cue.writeEnd){const p=Math.max(0,Math.min(1,(time-cue.writeStart)/(cue.writeEnd-cue.writeStart)));return (b.start+p*(b.end-b.start))/plan.total;}
  completed=b.end;
 }
 return 1;
}
export function narrationFrame(manifest,time,writingPlan){
 if(!manifest?.boards?.length)return null;
 const t=Math.max(0,Math.min(manifest.duration,time)),events=manifest.boards;
 const i=Math.max(0,events.findLastIndex(b=>b.start<=t)),b=events[i];
 let phase='hold',start=b.writeEnd,end=b.end;
 if(t<b.eraseStart){phase='lift';start=b.start;end=b.eraseStart;}
 else if(t<b.writeStart){phase='erase';start=b.eraseStart+1.8;end=b.writeStart;}
 else if(t<b.writeEnd){phase='write';start=b.writeStart;end=b.writeEnd;}
 const linear=Math.max(0,Math.min(1,(t-start)/Math.max(.001,end-start)));
 const progress=phase==='write'?(rowNarrationProgress(b.lineCues,t,writingPlan)??linear):linear;
 const writing=phase==='write'&&(!b.lineCues?.length||b.lineCues.some(c=>t>=c.writeStart&&t<c.writeEnd));
 return{page:b.page,phase,progress,writing,ended:t>=manifest.duration,duration:Math.max(.001,end-start)};
}
export function syncNarrationClock(clock,frame,slotFor){
 clock.page=frame.page;clock.active=slotFor(frame.page);clock.phase=frame.phase;clock.ended=frame.ended;
 const slots=Array.from({length:6},()=>({page:-1,progress:0}));
 const first=Math.max(0,frame.page-6),last=frame.phase==='lift'||frame.phase==='erase'?frame.page-1:frame.page;
 for(let p=first;p<=last;p++)slots[slotFor(p)]={page:p,progress:p===frame.page&&frame.phase==='write'?frame.progress:1};
 clock.slots=slots;const timingPage=frame.phase==='erase'?slots[clock.active].page:frame.page;
 clock.setDurations(timingPage,{...clock.timings.get(timingPage),[frame.phase]:frame.duration});
 clock.elapsed=frame.progress*frame.duration;
}
const formatTime=s=>Math.floor(s/60)+':'+String(Math.floor(s%60)).padStart(2,'0');
// Attached to the report hall's actual board. No separate screen or overlay.
export function createBoardVoicePanel(T,parent){
 const canvas=document.createElement('canvas');canvas.width=768;canvas.height=136;
 const ctx=canvas.getContext('2d'),texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;
 const material=new T.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false,toneMapped:false});
 const mesh=new T.Mesh(new T.PlaneGeometry(1.55,.274),material);mesh.position.set(1.69,-.817,.025);mesh.name='Existing chalkboard report voice control';mesh.userData={action:'voice:toggle',label:'报告语音 · AI 合成'};parent.add(mesh);mesh.visible=false;
 let last='',fade=1;
 function draw(state){
  const loading=state.phase==='loading'||state.phase==='buffering'||state.phase==='preparing',label=state.phase==='preparing'?'准备板书':loading?'报告语音加载':state.phase==='error'?'语音未就绪 · 重试':state.phase==='playing'?'Ⅱ  暂停报告':state.phase==='paused'?'▷  继续报告':state.phase==='ended'?'▷  重新聆听':'▷  聆听报告';
  const key=[label,state.progress,Math.floor(state.time),fade.toFixed(2)].join(':');if(key===last)return;last=key;
  ctx.clearRect(0,0,768,136);ctx.globalAlpha=fade;ctx.fillStyle='rgba(15,41,32,.9)';ctx.fillRect(0,0,768,136);ctx.fillStyle='#d6dfcd';ctx.font='400 31px "Microsoft YaHei",sans-serif';ctx.textAlign='left';ctx.fillText(label,28,53);
  ctx.textAlign='right';ctx.fillStyle='#acb8a4';ctx.font='26px Georgia,serif';ctx.fillText(loading?(state.progress===null?'…':Math.round(state.progress*100)+'%'):formatTime(state.time)+' / '+formatTime(state.duration),736,53);
  ctx.textAlign='left';ctx.font='19px "Microsoft YaHei",sans-serif';ctx.fillStyle='#8e9f8e';ctx.fillText('沈腾参考音色 · AI 合成',28,90);
  if(loading){ctx.fillStyle='#9ea58a35';ctx.fillRect(28,112,708,2);if(state.progress!==null){ctx.fillStyle='#d2c69a';ctx.fillRect(28,112,708*state.progress,2);}}
  ctx.globalAlpha=1;texture.needsUpdate=true;
 }
 return{mesh,update(state,dt,visible=true){mesh.visible=visible&&state.phase!=='idle';mesh.position.y=state.phase==='loading'?-.817:-1.19;mesh.updateMatrix();fade=state.phase==='loading'?1:Math.max(.8,fade-dt*.5);draw(state);},dispose(){mesh.parent?.remove(mesh);mesh.geometry.dispose();material.dispose();texture.dispose();}};
}
