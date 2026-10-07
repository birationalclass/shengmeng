// On-demand narration: no network or audio allocation until a report is selected.
export function createReportVoice({fetcher=globalThis.fetch,makeAudio=()=>new Audio(),makeURL=b=>URL.createObjectURL(b),revokeURL=u=>URL.revokeObjectURL(u),onChange=()=>{},baseURL=new URL('.',import.meta.url).href}={}){
 let epoch=0,attachToken=0,playToken=0,report=null,manifest=null,audio=null,desired=false,contextActive=true,controllers=new Set(),cache=new Map(),jobs=new Map(),index=0,offset=0;
 const state={report:null,phase:'idle',progress:null,time:0,duration:0,error:'',started:false,chapter:0,temporaryPause:false};
 const emit=()=>onChange({...state});
 const sync=()=>{if(audio&&manifest)state.time=Math.min(state.duration,manifest.chapters[index].start+audio.currentTime);return state.time;};
 function pause(){desired=false;state.temporaryPause=false;playToken++;sync();audio?.pause();if(['playing','buffering','preparing','away'].includes(state.phase)){state.phase='paused';emit();}}
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
  state.progress=1;state.temporaryPause=desired&&!contextActive;state.phase=state.temporaryPause?'away':state.started?'paused':'ready';state.error='';emit();return true;
 }
 async function play(){
  if(!audio)return false;const mine=epoch,token=++playToken,target=audio;desired=true;
  if(!contextActive){state.temporaryPause=true;state.phase='away';emit();return false;}state.temporaryPause=false;state.started=true;
  try{await target.play();if(mine!==epoch||token!==playToken||!desired||audio!==target){if(audio!==target||!desired||!contextActive)target.pause();return false;}state.phase='playing';state.error='';emit();return true;}
  catch{if(mine!==epoch||token!==playToken)return false;desired=false;state.phase='paused';state.error='点击黑板播放语音';emit();return false;}
 }
 async function advance(i){const resume=desired,mine=epoch;try{if(await attach(i)&&mine===epoch&&resume&&desired)await play();}catch(error){if(mine===epoch){desired=false;state.phase='error';state.error='语音下载失败 · 点击重试';emit();}}}
 async function select(next,{autoplay=false}={}){
  ++epoch;++attachToken;release();report=next;manifest=null;index=0;offset=0;const mine=epoch;
  desired=Boolean(autoplay&&next?.narration);Object.assign(state,{report:next?.id,phase:next?.narration?'loading':'idle',progress:null,time:0,duration:0,error:'',started:false,chapter:0,temporaryPause:false});emit();
  if(!next?.narration)return false;
  try{
   const src=new URL(next.narration.manifest,baseURL).href,controller=new AbortController();controllers.add(controller);
   let response;try{response=await fetcher(src,{signal:controller.signal,cache:"no-cache"});}finally{controllers.delete(controller);}
   if(!response.ok)throw Error('语音目录下载失败');const data=await response.json();if(mine!==epoch)return false;
   if(!data.chapters?.length||!data.boards?.length||!Number.isFinite(data.duration))throw Error('语音目录无效');
   manifest={...data,chapters:data.chapters.map(c=>({...c,src:new URL(c.src,src).href}))};state.duration=data.duration;
   const ready=await attach(0);if(ready&&desired)await play();return ready;
  }catch(error){if(mine!==epoch||error.name==='AbortError')return false;desired=false;state.temporaryPause=false;state.phase='error';state.error='语音未就绪 · 点击重试';emit();return false;}
 }
 async function seek(time){
  if(!manifest)return false;pause();const mine=epoch,target=Math.max(0,Math.min(manifest.duration,Number(time)||0));state.started=true;
  const i=Math.max(0,manifest.chapters.findLastIndex(c=>c.start<=target)),at=Math.min(manifest.chapters[i].duration-.025,target-manifest.chapters[i].start);
  try{if(audio&&i===index){audio.currentTime=Math.max(0,at);state.time=target;state.phase='paused';emit();return true;}return await attach(i,Math.max(0,at));}
  catch{if(mine===epoch){state.phase='error';state.error='语音定位失败 · 点击重试';emit();}return false;}
 }
 async function toggle(){
  if(['playing','buffering','preparing','away'].includes(state.phase)){pause();return true;}
  if(state.phase==='loading')return false;
  if(state.phase==='error'){if(!manifest)return select(report);try{return await attach(index,offset)&&await play();}catch{return false;}}
  if(state.phase==='ended')await seek(0);
  return play();
 }
 async function setContextActive(value){
  const next=Boolean(value);if(next===contextActive)return false;contextActive=next;
  if(!next){if(desired){playToken++;sync();audio?.pause();state.temporaryPause=true;state.phase='away';emit();}return false;}
  if(desired&&state.temporaryPause&&audio&&manifest){state.temporaryPause=false;return play();}
  return false;
 }
 return{state,select,toggle,pause,seek,setContextActive,
  async suspendUntil(job){
   if(!desired||state.phase==='preparing')return;
   const mine=epoch,token=++playToken;sync();audio?.pause();state.phase='preparing';state.progress=null;emit();
   try{await job;if(mine===epoch&&token===playToken&&desired)await play();}
   catch{if(mine===epoch&&token===playToken&&desired){pause();state.phase='error';state.error='板书尚未就绪 · 点击重试';emit();}}
  },get manifest(){return manifest;},
  update(){sync();if(manifest&&desired&&contextActive&&audio&&index+1<manifest.chapters.length&&manifest.chapters[index].duration-audio.currentTime<20){void load(index+1,false).catch(()=>{});}return state;},
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
export function reportVoicePresentation(state){
 const phase=state.phase,busy=phase==='loading';
 if(phase==='idle')return{message:'',buttonLabel:null,busy:false};
 const time=formatTime(state.time||0)+' / '+formatTime(state.duration||0);
 const message=busy?'报告语音加载 · '+(state.progress===null?'…':Math.round(state.progress*100)+'%'):phase==='error'?(state.error||'语音未就绪 · 点击重试'):phase==='ready'?'语音已就绪 · AI 合成 · '+formatTime(state.duration)+' · 点击聆听报告':phase==='away'?'暂离报告厅 · '+time:phase==='preparing'?'准备当前板书 · '+time:phase==='buffering'?'语音缓冲 · '+time:'报告 '+time;
 const buttonLabel=phase==='error'?'重试报告语音':['playing','buffering','preparing','away'].includes(phase)?'暂停报告':phase==='paused'?'继续报告':phase==='ended'?'重新聆听报告':'聆听报告';
 return{message,buttonLabel,busy};
}
// Language, playback and automatic camera share the board centre with separate hit targets.
export function reportControlLayout(column=0,withVoice=true){
 const center=22.4+5.6*Math.max(0,Math.min(2,column));
 return{center,language:{x:center-(withVoice?1.05:.55),y:-.16,z:-11.34,width:1.1},voice:{x:center,y:-.16,z:-11.302,width:.6},camera:{x:center+(withVoice?1.05:.55),y:-.16,z:-11.302,width:.6}};
}
export function reportVoiceIconPosition(column=0){return reportControlLayout(column).voice;}
const iconBusy=s=>['loading','buffering','preparing'].includes(s.phase)||s.phase==='away'&&!s.started;
const ease=t=>t*t*(3-2*t);
// Measured progress remains independent of shape animation; no fabricated completion.
export class VoiceIconMotion{
 constructor(){this.reset();}
 reset(){this.loading=false;this.finish=2;this.progress=0;this.spin=0;this.pause=0;this.chapter=-1;}
 update(state,dt){
  dt=Math.max(0,Math.min(.1,dt));this.spin+=dt;
  const busy=iconBusy(state),active=state.phase==='playing';
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
  const frame=motion.update(state,dt),busy=iconBusy(state);mesh.visible=visible&&state.phase!=='idle';mesh.userData.action=busy?null:'voice:toggle';mesh.userData.icon=frame.kind;mesh.userData.loadProgress=state.progress;
  mesh.userData.label=state.synthetic===false?(state.phase==='playing'?'暂停板书':'继续板书'):(reportVoicePresentation(state).buttonLabel||'聆听报告')+' · AI 合成';
  const key=[frame.kind,frame.ring.toFixed(3),frame.progress.toFixed(3),frame.pause.toFixed(3),frame.indeterminate?frame.spin.toFixed(2):''].join(':');
  if(key===last||!mesh.visible)return;last=key;ctx.clearRect(0,0,128,128);ctx.save();ctx.translate(64,64);ctx.scale(.72,.72);ctx.translate(-64,-64);ctx.strokeStyle='#f0e4ca';ctx.fillStyle='#f0e4ca';ctx.lineWidth=5;ctx.lineJoin='round';ctx.lineCap='round';
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
