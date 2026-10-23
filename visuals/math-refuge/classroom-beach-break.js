import {classroomBreakHour,classroomBreakTime} from './classroom-beach-time.js';
export const CLASSROOM_BEACH_ROUTES=Object.freeze([
 Object.freeze({id:'left',name:'左环漫滩'}),Object.freeze({id:'upper',name:'右上沙滩'}),Object.freeze({id:'lower',name:'右下沙滩'})
]);
export function randomBeachRoute(random=Math.random){return CLASSROOM_BEACH_ROUTES[Math.min(2,Math.max(0,Math.floor(random()*3)))];}
export function createClassroomBeachBreak({inPlace=false,onStart,onFinish,onCancel,onProgress,onState,onError,random=Math.random,now=()=>performance.now()}={}){
 if(!document.querySelector('link[data-classroom-beach-style]')){const style=document.createElement('link');style.rel='stylesheet';style.href=new URL('./classroom-beach-break.css?v=beach-camera-20261023-2',import.meta.url);style.dataset.classroomBeachStyle='';document.head.append(style);}
 if(!inPlace&&!document.querySelector('link[data-beach-preload]')){const warm=document.createElement('link');warm.rel='modulepreload';warm.href=new URL('./classroom-beach-viewer.bundle.js?v=beach-camera-20261023-2',import.meta.url);warm.fetchPriority='low';warm.dataset.beachPreload='';document.head.append(warm);}
 let active=null,frame=0,serial=0;
 const state=()=>active?{key:active.key,route:active.route.id,routeName:active.route.name,duration:active.duration,elapsed:active.elapsed,remaining:Math.max(0,active.duration-active.elapsed),playing:active.playing,resumeLecture:active.resumeLecture,ready:active.ready,prepared:active.prepared,phase:active.finishing?'returning':active.ready?'resting':active.prepared?'departing':'preparing',error:active.error||null,...classroomBreakTime(active.startHour,active.elapsed,active.duration)}:null;
 function notify(){if(!active)return;const s=state();active.timer.textContent=`${Math.floor(Math.ceil(s.remaining)/60)}:${String(Math.ceil(s.remaining)%60).padStart(2,'0')}`;active.panel.dataset.phase=s.error?'error':s.phase;active.panel.classList.toggle('ready-view',s.prepared);active.iframe?.contentWindow?.postMessage({type:'refuge-classroom-break-clock',token:active.token,elapsed:s.elapsed,startHour:s.startHour,duration:s.duration,phase:s.phase,playing:s.playing},location.origin);onState?.(s);onProgress?.(s);}
 function advance(stamp){if(!active)return;const a=active;if(a.ready&&a.playing&&!a.finishing)a.elapsed=Math.min(a.duration,a.elapsed+Math.max(0,stamp-a.stamp)/1000);a.stamp=stamp;}
 function step(){if(!active)return;const a=active;advance(now());notify();if(active===a&&a.ready&&a.playing&&!a.finishing&&a.elapsed>=a.duration)void finish();if(active)frame=requestAnimationFrame(step);}
 function pause({automatic=false}={}){if(!active)return;advance(now());active.autoPaused=automatic?(active.autoPaused||active.playing):false;active.playing=false;notify();}
 function play(){if(!active||active.error)return;active.autoPaused=false;active.stamp=now();active.playing=true;notify();}
 function seek(seconds){if(!active||active.finishing)return;active.elapsed=Math.max(0,Math.min(active.duration,Number(seconds)||0));active.stamp=now();notify();}
 function remove(){const a=active;if(!a)return null;active=null;serial++;cancelAnimationFrame(frame);clearTimeout(a.timeout);clearTimeout(a.returnTimeout);a.resolveReturned?.(false);a.panel.remove();document.body.classList.remove('classroom-beach-resting');removeEventListener('message',a.message);return a;}
 function cancel(){const saved=state(),a=remove();if(a)onCancel?.(saved);}
 async function finish({resume=active?.resumeLecture??false}={}){
  if(!active||active.finishing)return;const a=active,saved=state();a.finishing=true;a.playing=true;notify();
  try{
   if(!inPlace){a.returned=new Promise(resolve=>{a.resolveReturned=resolve;a.returnTimeout=setTimeout(()=>resolve(false),180000);});const returned=await a.returned;if(active!==a)return;if(!returned)throw Error('返回课堂的运镜未完成');}
   await onFinish?.({...saved,resume});
  }catch(error){onError?.(error.message);onCancel?.(saved);}finally{if(active===a)remove();}
 }
 async function start({key,duration=300,elapsed=0,playing=true,resumeLecture=playing,route,startHour=classroomBreakHour(),boardImage=null}={}){
  cancel();const token=String(++serial)+'-'+Math.random().toString(36).slice(2),chosen=CLASSROOM_BEACH_ROUTES.find(r=>r.id===route)||randomBeachRoute(random);
  const panel=document.createElement('section');panel.className='classroom-beach-break'+(inPlace?' in-place':'');panel.setAttribute('aria-label','课间休息');
  panel.innerHTML='<div class="beach-break-hold"></div><div class="beach-break-shade"></div><div class="beach-break-heading"><div>课间休息</div><time aria-live="off">5:00</time></div>';
  if(boardImage){const image=document.createElement('img');image.src=boardImage;image.alt='';panel.querySelector('.beach-break-hold').append(image);}
  const a=active={key,token,startHour,route:chosen,duration:Math.max(0,Number(duration)||300),elapsed:Math.max(0,Number(elapsed)||0),playing:Boolean(playing),resumeLecture:Boolean(resumeLecture),ready:false,prepared:inPlace,stamp:now(),panel,timer:panel.querySelector('time')};
  document.body.append(panel);document.body.classList.add('classroom-beach-resting');
  const ready=()=>{if(active!==a||a.finishing)return;a.prepared=true;a.ready=true;a.error=null;a.stamp=now();clearTimeout(a.timeout);notify();};
  const fail=error=>{if(active!==a)return;a.error=String(error?.message||error);a.playing=false;notify();onError?.(a.error);};
  a.message=event=>{if(event.origin!==location.origin||event.source!==a.iframe?.contentWindow||event.data?.token!==token)return;const type=event.data.type;
   if(type==='refuge-classroom-beach-image-request')a.iframe.contentWindow.postMessage({type:'refuge-classroom-beach-image',token,image:boardImage},location.origin);
   else if(type==='refuge-classroom-beach-prepared'){a.prepared=true;notify();}
   else if(type==='refuge-classroom-beach-ready')ready();
   else if(type==='refuge-classroom-beach-returned')a.resolveReturned?.(true);
   else if(type==='refuge-classroom-beach-error')fail(event.data.error);
  };
  notify();frame=requestAnimationFrame(step);
  if(inPlace){try{await onStart?.(state());ready();}catch(error){fail(error);}}
  else{const iframe=document.createElement('iframe');a.iframe=iframe;iframe.title=chosen.name;const url=new URL('./classroom-beach-viewer.html',import.meta.url);url.searchParams.set('route',chosen.id);url.searchParams.set('token',token);url.searchParams.set('hour',String(startHour));addEventListener('message',a.message);iframe.src=url;panel.prepend(iframe);a.timeout=setTimeout(()=>fail('沙滩场景未准备好，请重新进入本块课间。'),180000);}
  return state();
 }
 // With no transport controls on the scenery, an automatic background pause
 // resumes on focus; an explicit course pause remains paused.
 const blur=()=>{if(active?.iframe&&document.activeElement===active.iframe)return;pause({automatic:true});};
 const visibility=()=>{if(document.hidden)pause({automatic:true});else if(active?.autoPaused)play();};
 const focus=()=>{if(active?.autoPaused)play();};addEventListener('blur',blur);addEventListener('focus',focus);document.addEventListener('visibilitychange',visibility);
 return{start,pause,play,seek,finish,cancel,get state(){return state();},dispose(){cancel();removeEventListener('blur',blur);removeEventListener('focus',focus);document.removeEventListener('visibilitychange',visibility);}};
}
