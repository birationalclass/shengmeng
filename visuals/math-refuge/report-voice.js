import {createClassroomNativeMedia} from './classroom-native-media.js';
import {configureCoursePacks} from './course-pack-cache.js';
import {HandoffGate} from './handoff-gate.js?v=handoff-20261025';
import {BoardReview,boardReviewStart} from './board-review.js?v=uniform-review-20261019';
import {prepareClassroomAudioBlob} from './classroom-audio-decode.js?v=mp3-predecode-1';
import {primeClassroomAudio,disconnectClassroomAudio} from './classroom-audio-output.js?v=native-pcm-20261017-1';
import {selectClassroomOpening,classroomAudioRate} from './classroom-opening.js?v=uniform-review-20261019';
import {resourceFetch,createResourceFetch} from './resource-fetch.js';
import {createBackgroundAssets} from './background-assets.js';
import {trayControlLayout,placeTrayControl} from './board-tray-layout.js';
import {writingSchedule,scheduledWriting} from './board-work.js?v=uniform-review-20261019';
import {SCREEN_COLORS,CONTROL_VISUAL_SCALE} from './smart-screen-style.js?v=unframed-controls-1';
// On-demand narration: no network or audio allocation until a report is selected.
export function createReportVoice({fetcher=resourceFetch,makeAudio=()=>new Audio(),makeURL=b=>URL.createObjectURL(b),revokeURL=u=>URL.revokeObjectURL(u),prepareBoard=async()=>true,finishBoard=async()=>false,minimumBoardReview=true,onChange=()=>{},baseURL=new URL('.',import.meta.url).href,now=()=>performance.now()/1000,requestTimeout=15000,retryDelay=2000}={}){
 fetcher=createResourceFetch(fetcher,{idleTimeout:requestTimeout});
 let epoch=0,attachToken=0,playToken=0,report=null,manifest=null,audio=null,desired=false,contextActive=true,controllers=new Set(),cache=new Map(),jobs=new Map(),index=0,offset=0,playbackRate=1,boardHold=null;
 let manifestReady=Promise.resolve(null),resolveManifest=()=>{};
 let activity=null,segmentEnding=false,navigationIntent=false,navigationGate=null,retainAll=false,prefetchJob=null,assetsPreparing=false,boardReadiness=Promise.resolve(true);const blobs=new Map(),blobJobs=new Map();let preload={phase:'idle',completed:0,total:0,errors:[]};
 const state={report:null,phase:'idle',progress:null,time:0,duration:0,error:'',errorKind:'',started:false,chapter:0,temporaryPause:false,rate:1,activity:null};
 const nativeMedia=createClassroomNativeMedia(makeAudio);let mediaLease=null,mediaPrimed=false,audioListeners=[];
 function unbindAudio(){for(const [target,name,fn]of audioListeners)target.removeEventListener(name,fn);audioListeners=[];}
 const review=new BoardReview(now);let reviewTimer=null;const handoff=new HandoffGate();
 const emit=()=>{state.transportPlaying=desired&&contextActive&&!assetsPreparing;onChange({...state});};
 const chapterDisplayTime=(chapter,time)=>{
  const next=manifest.chapters[index+1],changesBoard=next&&(next.page??index+1)!==(chapter.page??index),end=chapter.start+chapter.duration;
  // The next board becomes current only when attach advances the chapter.
  return Math.min(state.duration,changesBoard?Math.max(chapter.start,end-.001):end,time);
 };

 const sync=()=>{if(audio&&manifest){const c=manifest.chapters[index],cue=handoff.check(audio.currentTime-(c.mediaStart||0),desired&&contextActive&&!assetsPreparing);if(cue){desired=false;navigationIntent=false;state.temporaryPause=false;playToken++;audio.currentTime=(c.mediaStart||0)+cue.at;audio.pause();state.phase='paused';state.manualPause=cue;queueMicrotask(emit);}state.time=chapterDisplayTime(c,c.start+Math.min(c.duration,Math.max(0,audio.currentTime-(c.mediaStart||0))));}if(activity&&manifest){if(activity.running){const stamp=now(),rate=manifest.chapters[index].activityType==='break'?1:playbackRate;activity.at=Math.min(activity.duration,activity.at+(stamp-activity.stamp)*rate);activity.stamp=stamp;}state.time=chapterDisplayTime(manifest.chapters[index],manifest.chapters[index].start+activity.at);state.activity={...manifest.chapters[index],remaining:Math.max(0,activity.duration-activity.at)};}if(audio&&manifest?.policy?.thinkingUsesRealSeconds&&(!mediaLease||mediaPrimed)){const c=manifest.chapters[index],b=manifest.boards.find(b=>b.page===c.page),at=audio.currentTime-(c.mediaStart||0),rate=classroomAudioRate(b,at,playbackRate);if(audio.playbackRate!==rate)audio.playbackRate=rate;}if(manifest){const b=manifest.boards.find(b=>b.page===(manifest.chapters[index].page??index));if(b&&!b.id?.endsWith('-break')&&state.time-b.start>=boardReviewStart(b))review.mark(b.page);}return state.time;};
 function pause(){sync();if(activity)activity.running=false;desired=false;navigationIntent=false;state.temporaryPause=false;playToken++;audio?.pause();if(['loading','playing','buffering','preparing','away'].includes(state.phase))state.phase='paused';emit();}
 const audioWarm=createBackgroundAssets({retryDelay,load:(job,signal)=>bytes(job.src,epoch,false,job.hint,signal)});
 function release(){handoff.reset();state.manualPause=null;clearTimeout(reviewTimer);review.clear();resolveManifest(null);pause();audioWarm.cancel();navigationGate=null;boardHold=null;disconnectClassroomAudio(audio);unbindAudio();nativeMedia.clear();mediaLease=null;mediaPrimed=false;audio=null;activity=null;state.activity=null;controllers.forEach(c=>c.abort());controllers.clear();for(const v of new Set(cache.values()))revokeURL(v);cache.clear();jobs.clear();blobs.clear();blobJobs.clear();retainAll=false;prefetchJob=null;preload={phase:'idle',completed:0,total:0,errors:[]};}
 async function fetchBytes(src,mine,show,sizeHint=0,signal){
  const controller=new AbortController();controllers.add(controller);
  const cancel=()=>controller.abort(signal.reason);signal?.addEventListener('abort',cancel,{once:true});if(signal?.aborted)cancel();
  try{
   const response=await fetcher(src,{signal:controller.signal,cache:"no-cache",priority:show?"high":"low"});if(!response.ok)throw Error('语音下载失败');
   const size=Number(response.headers.get('content-length'))||sizeHint,parts=[];let received=0;
   if(response.body?.getReader){const reader=response.body.getReader();for(;;){const {value,done}=await reader.read();if(done)break;if(mine!==epoch){await reader.cancel();return null;}parts.push(value);received+=value.byteLength;if(show){state.progress=size?Math.min(.99,received/size):null;emit();}}}
   else parts.push(await response.arrayBuffer());
   if(mine!==epoch)return null;return new Blob(parts,{type:response.headers?.get?.('content-type')||(/\.wav(?:[?#]|$)/i.test(src)?'audio/wav':'audio/mpeg')});
   }finally{signal?.removeEventListener('abort',cancel);controllers.delete(controller);}
 }
 async function bytes(src,mine,show,sizeHint=0,signal){
  if(blobs.has(src))return blobs.get(src);if(blobJobs.has(src)){if(show)fetcher.promote?.(src);return blobJobs.get(src);}
   const job=fetchBytes(src,mine,show,sizeHint,signal).then(blob=>{if(blob&&mine===epoch)blobs.set(src,blob);return blob;});blobJobs.set(src,job);try{return await job;}finally{if(blobJobs.get(src)===job)blobJobs.delete(src);}
 }
 function prefetchAll(){
   if(!manifest)return Promise.resolve(null);if(prefetchJob)return audioWarm.retry();retainAll=true;const ready=new Set([...cache.keys()].map(i=>manifest.chapters[i]?.src));
   for(const c of manifest.chapters)if(c.src&&!ready.has(c.src))audioWarm.add(c.src,'audio',c.bytes);prefetchJob=audioWarm.run();return prefetchJob;
 }
 function trim(){const retired=new Set(),retained=activity?manifest?.chapters[index+1]?.src:null;for(const [key,url] of cache)if((key<index||key>index+1)&&(!retained||manifest.chapters[key]?.src!==retained)){retired.add(url);cache.delete(key);}for(const url of retired)if(![...cache.values()].includes(url))revokeURL(url);if(!retainAll){const keep=new Set([...cache.keys()].map(i=>manifest.chapters[i]?.src));for(const src of blobs.keys())if(!keep.has(src))blobs.delete(src);}}
 async function load(i,show=true){
  if(manifest.chapters[i].kind==='activity')return null;
  if(cache.has(i))return cache.get(i);if(jobs.has(i)){if(show)fetcher.promote?.(manifest.chapters[i].src);return jobs.get(i);}
  for(const [key,url]of cache)if(manifest.chapters[key]?.src===manifest.chapters[i].src){cache.set(i,url);return url;}
  const mine=epoch,c=manifest.chapters[i];
  const job=(async()=>{const blob=await bytes(c.src,mine,show,c.bytes);if(!blob||mine!==epoch)return null;const playable=manifest.policy?.audioTransport==='mp3-predecode-pcm'?await prepareClassroomAudioBlob(blob,{expectedSeconds:c.mediaStart===undefined?c.duration:undefined}):blob;if(mine!==epoch)return null;const url=makeURL(playable);cache.set(i,url);trim();return url;})();
  jobs.set(i,job);try{return await job;}finally{if(jobs.get(i)===job)jobs.delete(i);}
 }
 async function attach(i,at=0){
  const mine=epoch,attachment=++attachToken;index=i;offset=at;handoff.reset(manifest.boards.find(b=>b.page===(manifest.chapters[i].page??i))?.manualPauses||[],at);state.manualPause=null;review.reset(manifest.chapters[i].page??i);audio?.pause();disconnectClassroomAudio(audio);unbindAudio();nativeMedia.detach();mediaLease=null;mediaPrimed=false;audio=null;activity=null;segmentEnding=false;state.activity=null;assetsPreparing=true;
  state.chapter=i;state.time=manifest.chapters[i].start+at;
  const page=manifest.chapters[i].page??manifest.boards.findLast(b=>b.start<=state.time)?.page??0,boardTime=state.time;
  boardReadiness=Promise.resolve().then(()=>prepareBoard(page,boardTime));boardReadiness.catch(()=>{});
  if(manifest.chapters[i].kind==='activity'){activity={at,stamp:now(),duration:manifest.chapters[i].duration,running:false,advancing:false};state.progress=1;state.temporaryPause=desired&&!contextActive;state.phase=state.temporaryPause?'away':state.started?'paused':'ready';sync();trim();emit();return true;}
  if(!cache.has(i)){if(desired||state.phase!=='paused')state.phase='loading';state.progress=null;emit();}
  const url=await load(i);if(!url||mine!==epoch||attachment!==attachToken)return false;trim();
  const nativePCM=manifest.policy?.audioTransport==='mp3-predecode-pcm',mediaAt=(manifest.chapters[i].mediaStart||0)+at;
  const lease=nativePCM?nativeMedia.attach(url,{at:mediaAt}):null,target=lease?.audio||makeAudio();audio=target;mediaLease=lease;
  const valid=()=>mine===epoch&&attachment===attachToken&&audio===target&&(!lease||lease.valid());
  const listen=(name,fn)=>{target.addEventListener(name,fn);audioListeners.push([target,name,fn]);};
  if(!lease){target.preload='auto';target.preservesPitch=true;target.playbackRate=playbackRate;target.src=url;const position=()=>{if(valid()&&mediaAt)target.currentTime=mediaAt;};listen('loadedmetadata',position);try{position();}catch{}}
  listen('timeupdate',()=>{if(valid()){sync();emit();}});
  listen('waiting',()=>{if(valid()&&desired){state.phase='buffering';emit();}});
  listen('playing',()=>{if(valid()&&desired){state.phase=boardHold?'preparing':'playing';emit();}});
  listen('error',()=>{if(valid()){desired=false;state.phase='error';state.error='语音未就绪 · 点击重试';emit();}});
  listen('ended',()=>{if(!valid()||segmentEnding||boardHold)return;sync();if(!desired)return;finishChapter();});
  if(lease&&(!await lease.ready||!valid()))return false;
  state.progress=1;state.temporaryPause=desired&&!contextActive;state.phase=state.temporaryPause?'away':state.started?'paused':'ready';state.error='';state.errorKind='';emit();return true;
 }
 async function play(){
  if(navigationGate){navigationIntent=true;navigationGate.token=playToken;state.phase="preparing";state.started=true;emit();return false;}
  if(!audio&&!activity){if(state.phase==='paused'&&(controllers.size||jobs.size)){desired=true;state.phase='loading';emit();}return false;}const mine=epoch,token=++playToken,target=audio,lease=mediaLease;desired=true;state.manualPause=null;
  if(!contextActive){state.temporaryPause=true;state.phase='away';emit();return false;}state.temporaryPause=false;state.started=true;
  if(boardHold){state.phase='preparing';emit();return false;}
  // Both the complete current audio blob and the matching prepared board are
  // mandatory. This gate covers autoplay, next chapter, seek, retry and re-entry.
  assetsPreparing=true;state.phase='preparing';emit();
  try{const ready=await boardReadiness;if(ready===false)throw Error('当前黑板尚未就绪');if(target&&(lease||manifest?.policy?.defaultPlaybackRate))await primeClassroomAudio(target,{signal:lease?.signal});}
  catch(error){if(mine===epoch&&token===playToken&&desired){pause();state.phase='error';state.errorKind='board';state.error=(error.message||'当前黑板加载失败')+' · 点击重试';emit();}return false;}
  if(mine!==epoch||token!==playToken||!desired||audio!==target||mediaLease!==lease){return false;}mediaPrimed=Boolean(lease);assetsPreparing=false;
  if(activity){activity.stamp=now();activity.running=true;state.phase='playing';state.error='';sync();emit();return true;}
  try{if(lease){const c=manifest.chapters[index],b=manifest.boards.find(b=>b.page===c.page);target.playbackRate=classroomAudioRate(b,target.currentTime-(c.mediaStart||0),playbackRate);}if(manifest?.policy?.thinkingUsesRealSeconds)sync();else if(!lease)target.playbackRate=playbackRate;if(!desired||token!==playToken)return false;await target.play();if(mine!==epoch||token!==playToken||!desired||audio!==target){if(audio!==target||!desired||!contextActive)target.pause();return false;}state.phase='playing';state.error='';state.errorKind='';emit();return true;}
  catch{if(mine!==epoch||token!==playToken)return false;desired=false;state.phase='paused';state.error='点击黑板播放语音';emit();return false;}
 }
 function finishChapter(){
  if(segmentEnding||boardHold||!manifest)return;
  segmentEnding=true;const mine=epoch,i=index,c=manifest.chapters[i],page=c.page??i,b=manifest.boards.find(b=>b.page===page),next=manifest.chapters[i+1];
  const proceed=()=>{if(i+1<manifest.chapters.length)return advance(i+1);else{desired=false;state.phase='ended';state.time=state.duration;emit();}};
  if(!minimumBoardReview||!b||b.id?.endsWith('-break')||(next&&(next.page??i+1)===page))return proceed();
  // Keep the old board selected until the final ink and real reading time finish.
  const hold={review:true};boardHold=hold;sync();audio?.pause();if(audio)audio.currentTime=(c.mediaStart||0)+c.duration-.001;state.time=Math.max(c.start,c.start+c.duration-.001);state.phase='preparing';emit();
  Promise.resolve().then(()=>finishBoard(page,state.time)).then(inkFinishedNow=>{
   if(mine!==epoch||boardHold!==hold)return;
   if(inkFinishedNow)review.reset(page);review.mark(page);
   const poll=()=>{
    if(mine!==epoch||boardHold!==hold)return;
    if(review.remaining(page)>0){reviewTimer=setTimeout(poll,Math.min(100,review.remaining(page)*1000));return;}
    if(!desired||!contextActive){reviewTimer=setTimeout(poll,100);return;}
    boardHold=null;proceed();
   };poll();
  }).catch(error=>{if(mine===epoch&&boardHold===hold){boardHold=null;pause();state.phase='error';state.error='板书完成检查失败 · 点击重试';emit();}});
 }
 async function advance(i){const resume=desired,mine=epoch,intent=playToken;try{if(await attach(i)&&mine===epoch&&resume&&desired)await play();}catch(error){if(mine===epoch&&intent===playToken){desired=false;state.phase='error';state.error='语音下载失败 · 点击重试';emit();}}}
 async function select(next,{autoplay=false}={}){
  ++epoch;++attachToken;release();manifestReady=new Promise(resolve=>resolveManifest=resolve);report=next;manifest=null;index=0;offset=0;const mine=epoch;
  desired=Boolean(autoplay&&next?.narration);Object.assign(state,{report:next?.id,contentKind:next?.kind==='classroom'?'classroom':'report',phase:next?.narration?'loading':'idle',progress:null,time:0,duration:0,error:'',errorKind:'',started:false,chapter:0,temporaryPause:false});emit();
  if(!next?.narration){resolveManifest(null);return false;}
  try{
   if(next.resourceIndex){await configureCoursePacks(next,{fetcher,base:baseURL});if(mine!==epoch)return false;}
   const src=new URL(next.narration.manifest,baseURL).href,controller=new AbortController();controllers.add(controller);
   let response;try{response=await fetcher(src,{signal:controller.signal,cache:"no-cache"});}finally{controllers.delete(controller);}
   if(!response.ok)throw Error('语音目录下载失败');const data=selectClassroomOpening(await response.json());if(mine!==epoch)return false;
   if(data.policy?.defaultPlaybackRate){playbackRate=data.policy.defaultPlaybackRate;state.rate=playbackRate;}
   if(!data.chapters?.length||!data.boards?.length||!Number.isFinite(data.duration))throw Error('语音目录无效');
   manifest={...data,chapters:data.chapters.map(c=>({...c,src:c.kind==='activity'?null:new URL(c.src,src).href}))};state.duration=data.duration;resolveManifest(manifest);
   const ready=await attach(0);if(ready&&desired)await play();return ready;
  }catch(error){if(mine!==epoch)return false;resolveManifest(null);if(error.name==='AbortError')return false;desired=false;state.temporaryPause=false;state.phase='error';state.error='语音未就绪 · 点击重试';emit();return false;}
 }
 async function seek(time,{preservePlayback=false,ready=null}={}){
  if(!manifest)return false;const resume=preservePlayback&&(desired||navigationIntent);pause();boardHold=null;navigationIntent=resume;const mine=epoch,intent=playToken,target=Math.max(0,Math.min(manifest.duration,Number(time)||0));state.started=true;const gate=navigationGate={token:intent};
  const i=Math.max(0,manifest.chapters.findLastIndex(c=>c.start<=target)),at=Math.min(manifest.chapters[i].duration-.025,target-manifest.chapters[i].start);
  const inkReady=Promise.resolve(ready);inkReady.catch(()=>{});
  try{let attached=true;if(activity&&i===index){activity.at=Math.max(0,at);activity.stamp=now();state.time=target;state.phase='paused';sync();emit();}else if(audio&&i===index){handoff.seek(at);state.manualPause=null;audio.currentTime=(manifest.chapters[i].mediaStart||0)+Math.max(0,at);state.time=target;state.phase='paused';emit();}else attached=await attach(i,Math.max(0,at));if(navigationGate===gate&&ready&&gate.token===playToken){state.phase=navigationIntent?'preparing':'paused';emit();}await inkReady;if(mine===epoch&&navigationGate===gate&&gate.token===playToken){const continuePlaying=navigationIntent;navigationGate=null;navigationIntent=false;if(attached&&continuePlaying)await play();}return attached;}
  catch{if(mine===epoch&&navigationGate===gate&&gate.token===playToken){navigationIntent=false;state.phase='error';state.error='语音定位失败 · 点击重试';emit();}return false;}finally{if(navigationGate===gate)navigationGate=null;}
 }
 async function toggle(){
  if(navigationGate){if(navigationIntent)pause();else await play();return true;}
  if(state.phase==='loading'&&desired){pause();return true;}
  if(['playing','buffering','preparing','away'].includes(state.phase)){pause();return true;}
  if(state.phase==='loading'){pause();return true;}
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
 return{state,select,toggle,pause,seek,setContextActive,prefetchAll,get mediaState(){return{...nativeMedia.state,primed:mediaPrimed,playbackRate:audio?.playbackRate??null};},get preloadState(){return audioWarm.state;},
  get transportPlaying(){return desired&&contextActive&&!assetsPreparing;},
  get boardHeld(){return Boolean(boardHold);},
  async holdForBoard(job,at){
   if(boardHold||!desired||(!audio&&!activity)||!manifest)return false;
   const mine=epoch,hold={};boardHold=hold;playToken++;sync();audio?.pause();if(activity)activity.running=false;
   const start=manifest.chapters[index].start;
   // A late handwriting gate may pause speech, but must never replay its onset.
   if(Number.isFinite(at))at=Math.max(at,state.time);
   if(Number.isFinite(at)&&at>=start&&at-start<manifest.chapters[index].duration){if(audio)audio.currentTime=(manifest.chapters[index].mediaStart||0)+at-start;else activity.at=at-start;state.time=at;}
   state.phase='preparing';state.temporaryPause=false;emit();
   try{await job;}finally{if(boardHold===hold){boardHold=null;if(mine===epoch&&desired&&contextActive){const c=manifest.chapters[index];if(audio&&audio.currentTime-(c.mediaStart||0)>=c.duration-.015){segmentEnding=false;await finishChapter();}else await play();}}}
   return true;
  },
  async skipActivity(){if(!activity||!manifest)return false;if(index+1<manifest.chapters.length){await advance(index+1);return true;}pause();state.phase='ended';state.time=state.duration;emit();return true;},
  setRate(value){sync();const n=Number(value);playbackRate=Number.isFinite(n)?Math.max(.75,Math.min(1.3,n)):1;state.rate=playbackRate;if(audio&&(!mediaLease||mediaPrimed)){audio.preservesPitch=true;audio.playbackRate=playbackRate;}emit();return playbackRate;},
  failForBoard(error){pause();boardHold=null;state.phase='error';state.errorKind='board';state.error=(error?.message||'板书下载失败')+' · 点击重试';emit();},
  async suspendUntil(job){
   if(!desired||state.phase==='preparing')return;
   const mine=epoch,token=++playToken;sync();if(activity)activity.running=false;audio?.pause();state.phase='preparing';state.progress=null;emit();
   try{await job;if(mine===epoch&&token===playToken&&desired)await play();}
   catch{if(mine===epoch&&token===playToken&&desired){pause();state.phase='error';state.error='板书尚未就绪 · 点击重试';emit();}}
  },get manifestReady(){return manifestReady;},get manifest(){return manifest;},
  update(){sync();if(audio&&desired&&!boardHold&&!segmentEnding&&manifest.chapters[index].mediaStart!==undefined&&audio.currentTime-(manifest.chapters[index].mediaStart||0)>=manifest.chapters[index].duration-.015){audio.pause();finishChapter();}if(activity&&activity.running&&!activity.advancing&&activity.at>=activity.duration){activity.advancing=true;activity.running=false;if(index+1<manifest.chapters.length)void advance(index+1);else{desired=false;state.phase='ended';state.time=state.duration;emit();}}if(manifest&&desired&&contextActive&&(audio||activity)&&index+1<manifest.chapters.length){const c=manifest.chapters[index],remaining=activity?activity.duration-activity.at:c.duration-(audio.currentTime-(c.mediaStart||0));if(remaining<20*playbackRate)void load(index+1,false).catch(()=>{});}return state;},
  dispose(){++epoch;release();nativeMedia.dispose();manifest=null;state.phase='idle';emit();}};
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
 else if(t<b.writeStart){phase=b.page<6?'lift':'erase';start=b.page<6?b.start:b.eraseStart+1.8;end=b.writeStart;}
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
 const buttonLabel=phase==='error'?(state.errorKind==='board'?'重试板书':'重试报告语音'):phase==='loading'?'暂停报告':['playing','buffering','preparing','away'].includes(phase)?'暂停报告':phase==='paused'?'继续报告':phase==='ended'?'重新聆听报告':'聆听报告';
 if(state.contentKind==='classroom')return{message:message.replaceAll('报告','课堂').replace('点击聆听课堂','点击开始上课'),buttonLabel:buttonLabel?.replaceAll('报告','课堂').replace('聆听课堂','开始上课'),busy};
 return{message,buttonLabel,busy};
}
export function narrationResourceBytes(manifest){return [...new Map((manifest?.chapters||[]).filter(c=>c.src).map(c=>[c.src,Number(c.bytes)||0])).values()].reduce((sum,n)=>sum+n,0);}
// Language, playback and automatic camera share the board centre with separate hit targets.
export function reportControlLayout(column=0,withVoice=true){return trayControlLayout(column);}
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
 function setColumn(value){column=value;const p=reportVoiceIconPosition(column);placeTrayControl(mesh,p);}
 setColumn(0);
 return{mesh,setColumn,update(state,dt,visible=true){
  const frame=motion.update(state,dt),busy=iconBusy(state);mesh.visible=visible&&state.phase!=='idle';mesh.userData.action='voice:toggle';mesh.userData.icon=frame.kind;mesh.userData.loadProgress=state.progress;
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
