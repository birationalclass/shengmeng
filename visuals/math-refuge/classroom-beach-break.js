import {classroomBreakHour,classroomBreakTime} from './classroom-beach-time.js';
export const CLASSROOM_BEACH_ROUTES=Object.freeze([
 Object.freeze({id:'left',name:'左环漫滩'}),
 Object.freeze({id:'upper',name:'右上沙滩'}),
 Object.freeze({id:'lower',name:'右下沙滩'})
]);
export function randomBeachRoute(random=Math.random){
 return CLASSROOM_BEACH_ROUTES[Math.min(2,Math.max(0,Math.floor(random()*3)))];
}
const pauseIcon='<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M8 5v14M16 5v14"/></svg>';
const playIcon='<svg viewBox="0 0 24 24" aria-hidden="true"><path d="m8 5 11 7-11 7Z"/></svg>';
const endIcon='<svg viewBox="0 0 24 24" aria-hidden="true"><path d="m4 5 10 7-10 7ZM19 5v14"/></svg>';

// The classroom owns the break. Visiting the coast never reloads its course,
// recreates its audio output, or unlocks a manually paused lesson.
export function createClassroomBeachBreak({inPlace=false,onStart,onFinish,onCancel,onProgress,onState,onError,random=Math.random,now=()=>performance.now()}={}){
 if(!document.querySelector('link[data-classroom-beach-style]')){
  const style=document.createElement('link');style.rel='stylesheet';style.href=new URL('./classroom-beach-break.css',import.meta.url);style.dataset.classroomBeachStyle='';document.head.append(style);
 }
 if(!inPlace&&!document.querySelector('link[data-beach-preload]')){const warm=document.createElement('link');warm.rel='modulepreload';warm.href=new URL('./classroom-beach-viewer.bundle.js?v=beach-day-fast-20261023',import.meta.url);warm.fetchPriority='low';warm.dataset.beachPreload='';document.head.append(warm);}
 let active=null,frame=0,serial=0;
 const state=()=>active?{key:active.key,route:active.route.id,routeName:active.route.name,duration:active.duration,elapsed:active.elapsed,remaining:Math.max(0,active.duration-active.elapsed),playing:active.playing,ready:active.ready,error:active.error||null,...classroomBreakTime(active.startHour,active.elapsed,active.duration)}:null;
 function notify(){if(!active)return;const s=state();active.timer.textContent=`${Math.floor(Math.ceil(s.remaining)/60)}:${String(Math.ceil(s.remaining)%60).padStart(2,'0')}`;active.pause.innerHTML=s.playing?pauseIcon:playIcon;active.pause.setAttribute('aria-label',s.playing?'暂停课间':'继续课间');active.pause.setAttribute('aria-pressed',String(!s.playing));active.panel.dataset.phase=s.error?'error':!s.ready?'loading':s.playing?'playing':'paused';if(active.iframe?.contentWindow)active.iframe.contentWindow.postMessage({type:'refuge-classroom-break-clock',token:active.token,elapsed:s.elapsed,startHour:s.startHour,duration:s.duration,playing:s.playing&&s.ready},location.origin);onState?.(s);onProgress?.(s);}
 function step(){if(!active)return;const stamp=now(),a=active;a.elapsed=Math.min(a.duration,a.elapsed+(a.ready&&a.playing?Math.max(0,stamp-a.stamp)/1000:0));a.stamp=stamp;notify();if(active===a&&a.ready&&a.playing&&a.elapsed>=a.duration){void finish();return;}frame=requestAnimationFrame(step);}
 function pause(){if(!active)return;const a=active,stamp=now();if(a.ready&&a.playing)a.elapsed=Math.min(a.duration,a.elapsed+Math.max(0,stamp-a.stamp)/1000);a.stamp=stamp;a.playing=false;notify();}
 function play(){if(!active||active.error)return;active.stamp=now();active.playing=true;notify();}
 function seek(seconds){if(!active)return;active.elapsed=Math.max(0,Math.min(active.duration,Number(seconds)||0));active.stamp=now();notify();}
 function remove(){const a=active;if(!a)return null;active=null;serial++;cancelAnimationFrame(frame);clearTimeout(a.timeout);a.panel.remove();document.body.classList.remove('classroom-beach-resting');removeEventListener('message',a.message);return a;}
 function cancel(){const saved=state(),a=remove();if(a)onCancel?.(saved);}
 async function finish({resume=active?.playing??false}={}){const saved=state(),a=remove();if(!a)return;await onFinish?.({...saved,resume});}
 async function start({key,duration=300,elapsed=0,playing=true,route,startHour=classroomBreakHour()}={}){
  cancel();const token=String(++serial)+'-'+Math.random().toString(36).slice(2),chosen=CLASSROOM_BEACH_ROUTES.find(r=>r.id===route)||randomBeachRoute(random);
  const panel=document.createElement('section');panel.className='classroom-beach-break'+(inPlace?' in-place':'');panel.setAttribute('aria-label','课间休息');
  panel.innerHTML='<div class="beach-break-shade"></div><div class="beach-break-heading"><div>课间休息</div><time aria-live="off">5:00</time></div><div class="beach-break-controls"><button type="button" data-break-pause></button><button type="button" data-break-end aria-label="结束课间，返回课堂">'+endIcon+'</button></div>';
  const a=active={key,token,startHour,route:chosen,duration:Math.max(0,Number(duration)||300),elapsed:Math.max(0,Number(elapsed)||0),playing:Boolean(playing),ready:false,stamp:now(),panel,timer:panel.querySelector('time'),pause:panel.querySelector('[data-break-pause]')};
  a.pause.onclick=()=>a.playing?pause():play();panel.querySelector('[data-break-end]').onclick=()=>finish({resume:a.playing});document.body.append(panel);document.body.classList.add('classroom-beach-resting');
  const ready=()=>{if(active!==a)return;a.ready=true;a.error=null;a.stamp=now();clearTimeout(a.timeout);notify();};
  const fail=error=>{if(active!==a)return;a.error=String(error?.message||error);a.playing=false;notify();onError?.(a.error);};
  a.message=event=>{if(event.origin!==location.origin||event.source!==a.iframe?.contentWindow||event.data?.token!==token)return;if(event.data.type==='refuge-classroom-beach-ready')ready();else if(event.data.type==='refuge-classroom-beach-error')fail(event.data.error);};
  if(inPlace){try{await onStart?.(state());ready();}catch(error){fail(error);}}
  else{const iframe=document.createElement('iframe');a.iframe=iframe;iframe.title=chosen.name;iframe.allow='fullscreen';const url=new URL('./classroom-beach-viewer.html',import.meta.url);url.searchParams.set('route',chosen.id);url.searchParams.set('token',token);url.searchParams.set('hour',String(startHour));iframe.src=url;panel.prepend(iframe);addEventListener('message',a.message);a.timeout=setTimeout(()=>fail('沙滩场景未准备好，请重新进入本块课间或返回课堂。'),180000);}
  notify();cancelAnimationFrame(frame);frame=requestAnimationFrame(step);return state();
 }
 const blur=()=>{if(active?.iframe&&document.activeElement===active.iframe)return;pause();};
 const visibility=()=>{if(document.hidden)pause();};addEventListener('blur',blur);document.addEventListener('visibilitychange',visibility);
 return {start,pause,play,seek,finish,cancel,get state(){return state();},dispose(){cancel();removeEventListener('blur',blur);document.removeEventListener('visibilitychange',visibility);}};
}
