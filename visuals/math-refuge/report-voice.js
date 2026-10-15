import {writingSchedule,scheduledWriting} from './board-work.js?v=continuous-classroom-1';
import {SCREEN_COLORS,CONTROL_VISUAL_SCALE} from './smart-screen-style.js?v=unframed-controls-1';
// On-demand narration: no network or audio allocation until a report is selected.
export function createReportVoice({fetcher=globalThis.fetch,makeAudio=()=>new Audio(),makeURL=b=>URL.createObjectURL(b),revokeURL=u=>URL.revokeObjectURL(u),onChange=()=>{},baseURL=new URL('.',import.meta.url).href,now=()=>performance.now()/1000}={}){
 let epoch=0,attachToken=0,playToken=0,report=null,manifest=null,audio=null,desired=false,contextActive=true,controllers=new Set(),cache=new Map(),jobs=new Map(),index=0,offset=0,playbackRate=1,boardHold=null;
 let activity=null,segmentEnding=false,navigationIntent=false,retainAll=false,prefetchJob=null;const blobs=new Map(),blobJobs=new Map();let preload={phase:'idle',completed:0,total:0,errors:[]};
 const state={report:null,phase:'idle',progress:null,time:0,duration:0,error:'',started:false,chapter:0,temporaryPause:false,rate:1,activity:null};
 const emit=()=>{state.transportPlaying=desired&&contextActive;onChange({...state});};
 const sync=()=>{if(audio&&manifest){const c=manifest.chapters[index];state.time=Math.min(state.duration,c.start+Math.min(c.duration,Math.max(0,audio.currentTime-(c.mediaStart||0))));}if(activity&&manifest){if(activity.running){const stamp=now(),rate=manifest.chapters[index].activityType==='break'?1:playbackRate;activity.at=Math.min(activity.duration,activity.at+(stamp-activity.stamp)*rate);activity.stamp=stamp;}state.time=manifest.chapters[index].start+activity.at;state.activity={...manifest.chapters[index],remaining:Math.max(0,activity.duration-activity.at)};}return state.time;};
 function pause(){sync();if(activity)activity.running=false;desired=false;navigationIntent=false;state.temporaryPause=false;playToken++;audio?.pause();if(['loading','playing','buffering','preparing','away'].includes(state.phase))state.phase='paused';emit();}
 function release(){pause();boardHold=null;audio=null;activity=null;state.activity=null;controllers.forEach(c=>c.abort());controllers.clear();for(const v of new Set(cache.values()))revokeURL(v);cache.clear();jobs.clear();blobs.clear();blobJobs.clear();retainAll=false;prefetchJob=null;preload={phase:'idle',completed:0,total:0,errors:[]};}
 async function fetchBytes(src,mine,show,sizeHint=0){
  const controller=new AbortController();controllers.add(controller);
  try{
   const response=await fetcher(src,{signal:controller.signal,cache:"no-cache"});if(!response.ok)throw Error('语音下载失败');
   const size=Number(response.headers.get('content-length'))||sizeHint,parts=[];let received=0;
   if(response.body?.getReader){const reader=response.body.getReader();for(;;){const {value,done}=await reader.read();if(done)break;if(mine!==epoch){await reader.cancel();return null;}parts.push(value);received+=value.byteLength;if(show){state.progress=size?Math.min(.99,received/size):null;emit();}}}
   else parts.push(await response.arrayBuffer());
   if(mine!==epoch)return null;return new Blob(parts,{type:'audio/mpeg'});
  }finally{controllers.delete(controller);}
 }
 async function bytes(src,mine,show,sizeHint=0){
  if(!retainAll)return fetchBytes(src,mine,show,sizeHint);
  if(blobs.has(src))return blobs.get(src);if(blobJobs.has(src))return blobJobs.get(src);
  const job=fetchBytes(src,mine,show,sizeHint).then(blob=>{if(blob&&mine===epoch)blobs.set(src,blob);return blob;});blobJobs.set(src,job);try{return await job;}finally{if(blobJobs.get(src)===job)blobJobs.delete(src);}
 }
 function prefetchAll(){
  if(!manifest)return Promise.resolve(null);if(prefetchJob)return prefetchJob;retainAll=true;const mine=epoch,ready=new Set([...cache.keys()].map(i=>manifest.chapters[i]?.src)),items=[...new Map(manifest.chapters.filter(c=>c.src&&!ready.has(c.src)).map(c=>[c.src,c])).values()];let cursor=0;preload={phase:'loading',completed:0,total:items.length,errors:[]};
  const job=Promise.all(Array.from({length:2},async()=>{while(mine===epoch&&cursor<items.length){const c=items[cursor++];try{await bytes(c.src,mine,false,c.bytes);}catch(e){if(mine===epoch&&e.name!=='AbortError')preload.errors.push(e.message);}if(mine===epoch)preload.completed++;}})).then(()=>{if(mine===epoch)preload.phase=preload.errors.length?'partial':'ready';return mine===epoch?{...preload}:null;});prefetchJob=job;return job;
 }
 function trim(){const retired=new Set(),retained=activity?manifest?.chapters[index+1]?.src:null;for(const [key,url] of cache)if((key<index||key>index+1)&&(!retained||manifest.chapters[key]?.src!==retained)){retired.add(url);cache.delete(key);}for(const url of retired)if(![...cache.values()].includes(url))revokeURL(url);}
 async function load(i,show=true){
  if(manifest.chapters[i].kind==='activity')return null;
  if(cache.has(i))return cache.get(i);if(jobs.has(i))return jobs.get(i);
  for(const [key,url]of cache)if(manifest.chapters[key]?.src===manifest.chapters[i].src){cache.set(i,url);return url;}
  const mine=epoch,c=manifest.chapters[i];
  const job=(async()=>{const blob=await bytes(c.src,mine,show,c.bytes);if(!blob||mine!==epoch)return null;const url=makeURL(blob);cache.set(i,url);trim();return url;})();
  jobs.set(i,job);try{return await job;}finally{if(jobs.get(i)===job)jobs.delete(i);}
 }
 async function attach(i,at=0){
  const mine=epoch,attachment=++attachToken;index=i;offset=at;audio?.pause();audio=null;activity=null;segmentEnding=false;state.activity=null;
  state.chapter=i;state.time=manifest.chapters[i].start+at;
  if(manifest.chapters[i].kind==='activity'){activity={at,stamp:now(),duration:manifest.chapters[i].duration,running:false,advancing:false};state.progress=1;state.temporaryPause=desired&&!contextActive;state.phase=state.temporaryPause?'away':state.started?'paused':'ready';sync();trim();emit();return true;}
  if(!cache.has(i)){if(desired||state.phase!=='paused')state.phase='loading';state.progress=null;emit();}
  const url=await load(i);if(!url||mine!==epoch||attachment!==attachToken)return false;trim();
  const target=makeAudio();audio=target;target.preload='auto';target.preservesPitch=true;target.playbackRate=playbackRate;target.src=url;
  const valid=()=>mine===epoch&&audio===target;
  const position=()=>{const mediaAt=(manifest.chapters[i].mediaStart||0)+at;if(valid()&&mediaAt){target.currentTime=mediaAt;}};
  target.addEventListener('loadedmetadata',position,{once:true});try{position();}catch{}
  target.addEventListener('timeupdate',()=>{if(valid()){sync();emit();}});
  target.addEventListener('waiting',()=>{if(valid()&&desired){state.phase='buffering';emit();}});
  target.addEventListener('playing',()=>{if(valid()&&desired){state.phase=boardHold?'preparing':'playing';emit();}});
  target.addEventListener('error',()=>{if(valid()){desired=false;state.phase='error';state.error='语音未就绪 · 点击重试';emit();}});
  target.addEventListener('ended',()=>{if(!valid()||segmentEnding||boardHold)return;segmentEnding=true;state.time=manifest.chapters[i].start+manifest.chapters[i].duration;if(i+1<manifest.chapters.length){void advance(i+1);}else{desired=false;state.phase='ended';state.time=state.duration;emit();}});
  state.progress=1;state.temporaryPause=desired&&!contextActive;state.phase=state.temporaryPause?'away':state.started?'paused':'ready';state.error='';emit();return true;
 }
 async function play(){
  if(!audio&&!activity){if(state.phase==='paused'&&(controllers.size||jobs.size)){desired=true;state.phase='loading';emit();}return false;}const mine=epoch,token=++playToken,target=audio;desired=true;
  if(!contextActive){state.temporaryPause=true;state.phase='away';emit();return false;}state.temporaryPause=false;state.started=true;
  if(boardHold){state.phase='preparing';emit();return false;}
  if(activity){activity.stamp=now();activity.running=true;state.phase='playing';state.error='';sync();emit();return true;}
  try{await target.play();if(mine!==epoch||token!==playToken||!desired||audio!==target){if(audio!==target||!desired||!contextActive)target.pause();return false;}state.phase='playing';state.error='';emit();return true;}
  catch{if(mine!==epoch||token!==playToken)return false;desired=false;state.phase='paused';state.error='点击黑板播放语音';emit();return false;}
 }
 async function advance(i){const resume=desired,mine=epoch;try{if(await attach(i)&&mine===epoch&&resume&&desired)await play();}catch(error){if(mine===epoch){desired=false;state.phase='error';state.error='语音下载失败 · 点击重试';emit();}}}
 async function select(next,{autoplay=false}={}){
  ++epoch;++attachToken;release();report=next;manifest=null;index=0;offset=0;const mine=epoch;
  desired=Boolean(autoplay&&next?.narration);Object.assign(state,{report:next?.id,contentKind:next?.kind==='classroom'?'classroom':'report',phase:next?.narration?'loading':'idle',progress:null,time:0,duration:0,error:'',started:false,chapter:0,temporaryPause:false});emit();
  if(!next?.narration)return false;
  try{
   const src=new URL(next.narration.manifest,baseURL).href,controller=new AbortController();controllers.add(controller);
   let response;try{response=await fetcher(src,{signal:controller.signal,cache:"no-cache"});}finally{controllers.delete(controller);}
   if(!response.ok)throw Error('语音目录下载失败');const data=await response.json();if(mine!==epoch)return false;
   if(!data.chapters?.length||!data.boards?.length||!Number.isFinite(data.duration))throw Error('语音目录无效');
   manifest={...data,chapters:data.chapters.map(c=>({...c,src:c.kind==='activity'?null:new URL(c.src,src).href}))};state.duration=data.duration;
   const ready=await attach(0);if(ready&&desired)await play();return ready;
  }catch(error){if(mine!==epoch||error.name==='AbortError')return false;desired=false;state.temporaryPause=false;state.phase='error';state.error='语音未就绪 · 点击重试';emit();return false;}
 }
 async function seek(time,{preservePlayback=false,ready=null}={}){
  if(!manifest)return false;const resume=preservePlayback&&(desired||navigationIntent);pause();boardHold=null;navigationIntent=resume;const mine=epoch,intent=playToken,target=Math.max(0,Math.min(manifest.duration,Number(time)||0));state.started=true;
  const i=Math.max(0,manifest.chapters.findLastIndex(c=>c.start<=target)),at=Math.min(manifest.chapters[i].duration-.025,target-manifest.chapters[i].start);
  try{let attached=true;if(activity&&i===index){activity.at=Math.max(0,at);activity.stamp=now();state.time=target;state.phase='paused';sync();emit();}else if(audio&&i===index){audio.currentTime=(manifest.chapters[i].mediaStart||0)+Math.max(0,at);state.time=target;state.phase='paused';emit();}else attached=await attach(i,Math.max(0,at));await ready;if(mine===epoch&&intent===playToken){navigationIntent=false;if(attached&&resume)await play();}return attached;}
  catch{if(mine===epoch&&intent===playToken){navigationIntent=false;state.phase='error';state.error='语音定位失败 · 点击重试';emit();}return false;}
 }
 async function toggle(){
  if(state.phase==='loading'&&desired){pause();return true;}
  if(['playing','buffering','preparing','away'].includes(state.phase)){pause();return true;}
  if(state.phase==='loading')return false;
  if(state.phase==='error'){if(!manifest)return select(report);try{return await attach(index,offset)&&await play();}catch{return false;}}
  if(state.phase==='ended')await seek(0);
  return play();
 }
 async function setContextActive(value){
  const next=Boolean(value);if(next===contextActive)return false;contextActive=next;
  if(!next){if(desired){playToken++;sync();if(activity)activity.running=false;audio?.pause();state.temporaryPause=true;state.phase='away';emit();}return false;}
  if(desired&&state.temporaryPause&&(audio||activity)&&manifest){state.temporaryPause=false;return play();}
  return false;
 }
 return{state,select,toggle,pause,seek,setContextActive,prefetchAll,get preloadState(){return{...preload,errors:[...preload.errors]};},
  get transportPlaying(){return desired&&contextActive;},
  get boardHeld(){return Boolean(boardHold);},
  async holdForBoard(job,at){
   if(boardHold||!desired||(!audio&&!activity)||!manifest)return false;
   const mine=epoch,hold={};boardHold=hold;playToken++;sync();audio?.pause();if(activity)activity.running=false;
   const start=manifest.chapters[index].start;
   if(Number.isFinite(at)&&at>=start&&at-start<manifest.chapters[index].duration){if(audio)audio.currentTime=(manifest.chapters[index].mediaStart||0)+at-start;else activity.at=at-start;state.time=at;}
   state.phase='preparing';state.temporaryPause=false;emit();
   try{await job;}finally{if(boardHold===hold){boardHold=null;if(mine===epoch&&desired&&contextActive){const c=manifest.chapters[index];if(audio&&audio.currentTime-(c.mediaStart||0)>=c.duration-.015){if(index+1<manifest.chapters.length)await advance(index+1);else{desired=false;state.phase='ended';state.time=state.duration;emit();}}else await play();}}}
   return true;
  },
  async skipActivity(){if(!activity||!manifest)return false;if(index+1<manifest.chapters.length){await advance(index+1);return true;}pause();state.phase='ended';state.time=state.duration;emit();return true;},
  setRate(value){sync();const n=Number(value);playbackRate=Number.isFinite(n)?Math.max(.75,Math.min(1.3,n)):1;state.rate=playbackRate;if(audio){audio.preservesPitch=true;audio.playbackRate=playbackRate;}emit();return playbackRate;},
  async suspendUntil(job){
   if(!desired||state.phase==='preparing')return;
   const mine=epoch,token=++playToken;sync();if(activity)activity.running=false;audio?.pause();state.phase='preparing';state.progress=null;emit();
   try{await job;if(mine===epoch&&token===playToken&&desired)await play();}
   catch{if(mine===epoch&&token===playToken&&desired){pause();state.phase='error';state.error='板书尚未就绪 · 点击重试';emit();}}
  },get manifest(){return manifest;},
  update(){sync();if(audio&&desired&&!boardHold&&!segmentEnding&&manifest.chapters[index].mediaStart!==undefined&&audio.currentTime-(manifest.chapters[index].mediaStart||0)>=manifest.chapters[index].duration-.015){segmentEnding=true;audio.pause();if(index+1<manifest.chapters.length)void advance(index+1);else{desired=false;state.phase='ended';state.time=state.duration;emit();}}if(activity&&activity.running&&!activity.advancing&&activity.at>=activity.duration){activity.advancing=true;activity.running=false;if(index+1<manifest.chapters.length)void advance(index+1);else{desired=false;state.phase='ended';state.time=state.duration;emit();}}if(manifest&&desired&&contextActive&&(audio||activity)&&index+1<manifest.chapters.length){const c=manifest.chapters[index],remaining=activity?activity.duration-activity.at:c.duration-(audio.currentTime-(c.mediaStart||0));if(remaining<20*playbackRate)void load(index+1,false).catch(()=>{});}return state;},
  dispose(){++epoch;release();manifest=null;state.phase='idle';emit();}};
}
// Use the same measured stroke costs as chalkPosition and inkReveal, so a
// long formula is never treated as one equal-sized slice of a whole board.
const lineCostBounds=new WeakMap();
function cueWriteDuration(cue,plan,bounds){const available=cue.writeEnd-cue.writeStart;return (plan?.physicalTiming||plan?.chineseStrokeTiming)&&bounds?(bounds.end-bounds.start)/plan.unitsPerSecond:available;}
export function rowNarrationProgress(cues,time,plan){
 if(!cues?.length||!plan?.total)return null;
 if(plan.physicalTiming)return scheduledWriting(writingSchedule({writeStart:cues[0].writeStart,lineCues:cues},plan),time).progress;
 let bounds=lineCostBounds.get(plan);if(!bounds){bounds=new Map();
 for(const s of plan.segments){if(!Number.isInteger(s.mainLine))continue;const b=bounds.get(s.mainLine);if(b)b.end=s.end;else bounds.set(s.mainLine,{start:s.start,end:s.end});}
 lineCostBounds.set(plan,bounds);}
 let completed=0;
 for(const cue of cues){
  const b=bounds.get(cue.row);if(!b)throw Error('Narration row has no visible ink: '+cue.row);
  if(time<cue.writeStart)return completed/plan.total;
  if(time<cue.writeEnd){const p=Math.max(0,Math.min(1,(time-cue.writeStart)/Math.max(.001,cueWriteDuration(cue,plan,b))));return (b.start+p*(b.end-b.start))/plan.total;}
  completed=b.end;
 }
 return 1;
}
export function narrationFrame(manifest,time,writingPlan,erasePlan){
 if(!manifest?.boards?.length)return null;
 const t=Math.max(0,Math.min(manifest.duration,time)),events=manifest.boards;
 const i=Math.max(0,events.findLastIndex(b=>b.start<=t)),b=events[i];
 const schedule=writingSchedule(b,writingPlan);
 if(schedule&&t>=b.writeStart){const ink=scheduledWriting(schedule,t);return{page:b.page,phase:ink.progress<1?'write':'hold',...ink,ended:t>=manifest.duration,duration:Math.max(.001,schedule.end-b.writeStart)};}
 let phase='hold',start=b.writeEnd,end=b.end;
 if(t<b.eraseStart){phase='lift';start=b.start;end=b.eraseStart;}
 else if(t<b.writeStart){phase='erase';start=b.eraseStart+1.8;end=b.writeStart;}
 else if(t<b.writeEnd){phase='write';start=b.writeStart;end=b.writeEnd;}
 const linear=Math.max(0,Math.min(1,(t-start)/Math.max(.001,end-start)));
 const natural=(writingPlan?.physicalTiming||writingPlan?.chineseStrokeTiming)?writingPlan.total/writingPlan.unitsPerSecond:end-start;
 const progress=phase==='write'?(rowNarrationProgress(b.lineCues,t,writingPlan)??Math.max(0,Math.min(1,(t-start)/Math.max(.001,natural)))):linear;
 const writing=phase==='write'&&(!b.lineCues?.length?t<start+natural:b.lineCues.some(c=>t>=c.writeStart&&t<c.writeStart+cueWriteDuration(c,writingPlan,lineCostBounds.get(writingPlan)?.get(c.row))));
 return{page:b.page,phase,progress:phase==='erase'&&erasePlan?Math.max(0,Math.min(1,(t-start)/erasePlan.duration)):progress,writing,ended:t>=manifest.duration,duration:phase==='erase'&&erasePlan?erasePlan.duration:Math.max(.001,end-start)};
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
export function reportVoicePresentation(state){
 const phase=state.phase,busy=phase==='loading';
 if(phase==='idle')return{message:'',buttonLabel:null,busy:false};
 const time=formatTime(state.time||0)+' / '+formatTime(state.duration||0);
 const message=busy?'报告语音加载 · '+(state.progress===null?'…':Math.round(state.progress*100)+'%'):phase==='error'?(state.error||'语音未就绪 · 点击重试'):phase==='ready'?'语音已就绪 · AI 合成 · '+formatTime(state.duration)+' · 点击聆听报告':phase==='away'?'暂离报告厅 · '+time:phase==='preparing'?'准备当前板书 · '+time:phase==='buffering'?'语音缓冲 · '+time:'报告 '+time;
 const buttonLabel=phase==='error'?'重试报告语音':['playing','buffering','preparing','away'].includes(phase)?'暂停报告':phase==='paused'?'继续报告':phase==='ended'?'重新聆听报告':'聆听报告';
 if(state.contentKind==='classroom')return{message:message.replaceAll('报告','课堂').replace('点击聆听课堂','点击开始上课'),buttonLabel:buttonLabel?.replaceAll('报告','课堂').replace('聆听课堂','开始上课'),busy};
 return{message,buttonLabel,busy};
}
export function narrationResourceBytes(manifest){return [...new Map((manifest?.chapters||[]).filter(c=>c.src).map(c=>[c.src,Number(c.bytes)||0])).values()].reduce((sum,n)=>sum+n,0);}
// Language, playback and automatic camera share the board centre with separate hit targets.
export function reportControlLayout(column=0,withVoice=true){
 const center=22.4+5.6*Math.max(0,Math.min(2,column));
 return{center,previous:{x:center-.94,y:-.02,z:-11.302,width:.6},next:{x:center+.94,y:-.02,z:-11.302,width:.6},language:{x:center-1.94,y:-.02,z:-11.34,width:1.1},voice:{x:center,y:-.02,z:-11.302,width:.6},camera:{x:center+1.94,y:-.02,z:-11.302,width:.6},zoomOut:{x:center+2.47,y:.15,z:-11.302,width:.34,height:.3},zoomIn:{x:center+2.47,y:-.19,z:-11.302,width:.34,height:.3},reveal:{x:center+1.5,y:-.54,z:-11.302,width:.6}};
}
export function reportVoiceIconPosition(column=0){return reportControlLayout(column).voice;}
const iconBusy=s=>(['loading','buffering','preparing'].includes(s.phase)&&!(s.transportPlaying&&s.started))||s.phase==='away'&&!s.started;
const ease=t=>t*t*(3-2*t);
// Measured progress remains independent of shape animation; no fabricated completion.
export class VoiceIconMotion{
 constructor(){this.reset();}
 reset(){this.loading=false;this.finish=2;this.progress=0;this.spin=0;this.pause=0;this.chapter=-1;}
 update(state,dt){
  dt=Math.max(0,Math.min(.1,dt));this.spin+=dt;
  const busy=iconBusy(state),active=state.transportPlaying??state.phase==='playing';
  if(state.phase==='idle'){this.reset();return{kind:'play',ring:0,progress:0,pause:0,spin:0};}
  if(busy){if(!this.loading||state.chapter!==this.chapter)this.progress=0;this.loading=true;this.finish=0;this.chapter=state.chapter;
   if(state.progress!==null&&Number.isFinite(state.progress))this.progress+=(Math.max(this.progress,state.progress)-this.progress)*(1-Math.exp(-dt*16));this.pause=0;
  }else{if(this.loading){this.loading=false;this.finish=0;}this.finish+=dt;this.progress+=(1-this.progress)*(1-Math.exp(-dt*26));}
  const ring=busy?1:1-ease(Math.min(1,Math.max(0,(this.finish-.12)/.45)));
  const targetPause=active&&!busy&&this.finish>=.77?1:0;this.pause+=(targetPause-this.pause)*(1-Math.exp(-dt*20));
  return{kind:busy||ring>.999?'ring':ring>.001?'morph':this.pause>.5?'pause':'play',ring,progress:this.progress,pause:this.pause,spin:this.spin,indeterminate:busy&&state.progress===null};
 }
}
export function createBoardVoicePanel(T,parent){
 const canvas=document.createElement('canvas');canvas.width=canvas.height=128;
 const ctx=canvas.getContext('2d'),texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;
 const material=new T.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false,toneMapped:false});
 const mesh=new T.Mesh(new T.PlaneGeometry(.6,.6),material);mesh.name='Smart glass report play icon';mesh.userData={action:'voice:toggle',label:'聆听报告 · AI 合成',smartGlass:true};parent.add(mesh);mesh.visible=false;
 const motion=new VoiceIconMotion(),vertices=[[43,29],[94,64],[43,99]],count=72;
 const circle=Array.from({length:count+1},(_,i)=>{const a=-Math.PI/2+i/count*Math.PI*2;return[64+35*Math.cos(a),64+35*Math.sin(a)];});
 const triangle=Array.from({length:count+1},(_,i)=>{const side=Math.min(2,Math.floor(i/(count/3))),t=(i-side*count/3)/(count/3),a=vertices[side],b=vertices[(side+1)%3];return[a[0]+(b[0]-a[0])*t,a[1]+(b[1]-a[1])*t];});
 let last='',column=0;
 function setColumn(value){column=value;const p=reportVoiceIconPosition(column);mesh.position.set(p.x,p.y,p.z);mesh.updateMatrix();}
 setColumn(0);
 return{mesh,setColumn,update(state,dt,visible=true){
  const frame=motion.update(state,dt),busy=iconBusy(state);mesh.visible=visible&&state.phase!=='idle';mesh.userData.action=busy&&!state.transportPlaying?null:'voice:toggle';mesh.userData.icon=frame.kind;mesh.userData.loadProgress=state.progress;
  mesh.userData.label=state.synthetic===false?(state.phase==='playing'?'暂停板书':'继续板书'):(reportVoicePresentation(state).buttonLabel||'聆听报告')+' · AI 合成';
  const key=[frame.kind,frame.ring.toFixed(3),frame.progress.toFixed(3),frame.pause.toFixed(3),frame.indeterminate?frame.spin.toFixed(2):''].join(':');
  if(key===last||!mesh.visible)return;last=key;ctx.clearRect(0,0,128,128);ctx.save();ctx.translate(64,64);ctx.scale(.72*CONTROL_VISUAL_SCALE,.72*CONTROL_VISUAL_SCALE);ctx.translate(-64,-64);ctx.strokeStyle=SCREEN_COLORS.text;ctx.fillStyle=SCREEN_COLORS.text;ctx.lineWidth=4;ctx.lineJoin='miter';ctx.lineCap='square';
  ctx.globalAlpha=1-frame.pause;
  if(busy||frame.ring>.999){ctx.globalAlpha=.18;ctx.beginPath();ctx.arc(64,64,35,0,Math.PI*2);ctx.stroke();ctx.globalAlpha=1;ctx.beginPath();const start=frame.indeterminate?frame.spin*2-Math.PI/2:-Math.PI/2,length=frame.indeterminate?Math.PI*.55:Math.PI*2*frame.progress;ctx.arc(64,64,35,start,start+Math.max(.02,length));ctx.stroke();}
  else{ctx.beginPath();for(let i=0;i<=count;i++){const a=circle[i],b=triangle[i],x=b[0]+(a[0]-b[0])*frame.ring,y=b[1]+(a[1]-b[1])*frame.ring;i?ctx.lineTo(x,y):ctx.moveTo(x,y);}ctx.closePath();ctx.stroke();}
  if(frame.pause>.001){ctx.globalAlpha=frame.pause;ctx.fillRect(40,30,12,68);ctx.fillRect(76,30,12,68);}ctx.globalAlpha=1;ctx.restore();texture.needsUpdate=true;
 },dispose(){mesh.parent?.remove(mesh);mesh.geometry.dispose();mesh.material.dispose();texture.dispose();}};
}


// Voice variants have independent timings. Keep the same spoken semantic segment.
export function mapNarrationPosition(previous,next,time){
 const old=previous?.paragraphs?.find(p=>p.start<=time&&p.end>time);
 const cue=old&&next?.paragraphs?.find(p=>p.page===old.page&&p.role===old.role&&p.section===old.section&&(Number.isInteger(old.row)?p.row===old.row:p.paragraph===old.paragraph));
 if(cue)return cue.start+Math.max(0,Math.min(1,(time-old.start)/Math.max(.001,old.end-old.start)))*(cue.end-cue.start);
 const board=old&&next?.boards?.find(b=>b.page===old.page);if(board)return board.writeStart;
 return Math.max(0,Math.min(next?.duration||0,time/Math.max(1,previous?.duration||next?.duration||1)*(next?.duration||0)));
}

// Losing foreground focus is an explicit pause; focusing never resumes playback.
export function bindVoiceFocusPause(voice,{documentTarget=globalThis.document,windowTarget=globalThis.window}={}){
 const blur=()=>voice.pause(),hidden=()=>{if(documentTarget.hidden)voice.pause();};
 windowTarget.addEventListener('blur',blur);documentTarget.addEventListener('visibilitychange',hidden);
 return()=>{windowTarget.removeEventListener('blur',blur);documentTarget.removeEventListener('visibilitychange',hidden);};
}
