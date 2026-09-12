// A cancellable timeline separates one-shot entrances from demonstrations.
// Only demonstrations use autoplay, delay, looping and the dismiss control.
// Hover, proof tabs and resize never arm either kind.
export function createAnimationPlayback({language,ready,play,stop,prepare=()=>{},settle=()=>{},enter=play,prepareEntrance=()=>{}}) {
 const defaults={autoplay:true,loop:true,delay:2,interval:5},storageKey='spectral-animation-playback';
 const $=s=>document.querySelector(s),reduced=matchMedia('(prefers-reduced-motion:reduce)');
 let settings={...defaults},context=null,controller=null,phase='idle',serial=0,plays=0,lastLanguage=null,runKind=null;
 try {const saved=JSON.parse(localStorage.getItem(storageKey));for(const k of ['autoplay','loop'])if(typeof saved?.[k]==='boolean')settings[k]=saved[k];for(const [k,max] of [['delay',5],['interval',10]])if(Number.isFinite(saved?.[k]))settings[k]=Math.max(0,Math.min(max,saved[k]));}catch{}
 const t=(zh,en)=>language()==='en'?en:zh,close=$('#hideDiagramAnimation');
 function publish(){close.hidden=runKind!=='demonstration'||!['playing','interval','complete'].includes(phase);close.setAttribute('aria-label',t('隐藏当前动画','Hide current animation'));close.title=t('隐藏当前动画','Hide current animation');window.spectralPlayback={phase,serial,plays,kind:runKind,key:context?.key,settings:{...settings}};}
 function waitUntil(test,signal){return new Promise(resolve=>{let frame=0;const end=value=>{cancelAnimationFrame(frame);signal.removeEventListener('abort',cancel);resolve(value);},cancel=()=>end(false);signal.addEventListener('abort',cancel,{once:true});const tick=()=>{if(signal.aborted)return end(false);if(test())return end(true);frame=requestAnimationFrame(tick);};tick();});}
 function wait(ms,signal){return new Promise(resolve=>{const id=setTimeout(()=>end(true),ms),end=value=>{clearTimeout(id);signal.removeEventListener('abort',cancel);resolve(value);},cancel=()=>end(false);if(signal.aborted)cancel();else signal.addEventListener('abort',cancel,{once:true});});}
 function cancel(){controller?.abort();controller=null;stop();}
 async function arm(manual=false,kind=context?.kind||'demonstration',withEntrance=false){
  cancel();runKind=kind;serial++;const entrance=kind==='entrance'||withEntrance&&context?.hasEntrance;if(!context?.key||!entrance&&!settings.autoplay&&!manual){phase='idle';settle();publish();return;}
  const run=controller=new AbortController(),signal=run.signal;
  if(entrance)prepareEntrance();
  if(kind==='demonstration')prepare();phase='waiting';publish();
  if(!await waitUntil(()=>ready()&&!document.hidden,signal))return;
  if(entrance){
   if(!await waitUntil(()=>!$('#motionSettings').open,signal))return;
   phase='entering';publish();
   await enter({signal,waitUntil:test=>waitUntil(test,signal),wait:ms=>wait(ms,signal)});
   if(signal.aborted)return;if(kind==='entrance'){phase='complete';publish();return;}
   if(!settings.autoplay&&!manual){phase='idle';publish();return;}phase='waiting';publish();
  }
  if(!await wait(settings.delay*1000,signal))return;
  do {
   if(!await waitUntil(()=>!document.hidden&&!$('#motionSettings').open,signal))return;
   phase='playing';plays++;publish();
   await play({signal,waitUntil:test=>waitUntil(test,signal),wait:ms=>wait(ms,signal)});
   if(signal.aborted)return;
   if(!settings.loop||reduced.matches){phase='complete';publish();return;}
   phase='interval';publish();
   if(!await wait(settings.interval*1000,signal))return;
   if(signal.aborted)return;stop();
   // Even a static or empty scene yields a painted frame between zero-gap runs.
   let painted=false;requestAnimationFrame(()=>{painted=true;});if(!await waitUntil(()=>painted,signal))return;
  }while(!signal.aborted);
 }
 function syncSettings(){
  lastLanguage=language();
  $('#playbackTitle').textContent=t('演示动画','Demonstration animations');
  $('#playbackAutoLabel').textContent=t('自动播放','Autoplay');$('#playbackLoopLabel').textContent=t('循环播放','Loop');
  $('#playbackDelayLabel').textContent=t('显示完成后等待','Delay after card appears');$('#playbackIntervalLabel').textContent=t('播放结束后间隔','Interval after playback');
  for(const name of ['autoplay','loop'])$('#playback-'+name).checked=settings[name];
  for(const name of ['delay','interval']){$('#playback-'+name).value=settings[name];$('#playback-'+name+'-value').textContent=settings[name]+t(' 秒',' s');}
  $('#playback-interval').disabled=!settings.loop;
  $('#playbackHint').textContent=t('出场动画进入时仅播放一次，不受这些设置影响。关闭演示自动播放后，点击当前主卡片可播放；减弱动态效果时不循环。','Entrance effects play once on entry, independently of these settings. With demonstration autoplay off, click the current card to play. Reduced motion disables looping.');publish();
 }
 function update(){for(const k of ['autoplay','loop'])settings[k]=$('#playback-'+k).checked;for(const k of ['delay','interval'])settings[k]=Number($('#playback-'+k).value);try{localStorage.setItem(storageKey,JSON.stringify(settings));}catch{}syncSettings();if(context?.kind!=='entrance')arm();}
 for(const k of ['autoplay','loop','delay','interval'])$('#playback-'+k).addEventListener('change',update);
 for(const k of ['delay','interval'])$('#playback-'+k).addEventListener('input',()=>{$('#playback-'+k+'-value').textContent=$('#playback-'+k).value+t(' 秒',' s');});
 close.addEventListener('click',event=>{event.stopPropagation();cancel();phase='hidden';publish();});
 $('#motionReset').addEventListener('click',()=>{settings={...defaults};try{localStorage.setItem(storageKey,JSON.stringify(settings));}catch{}syncSettings();if(context?.kind!=='entrance')arm();});
 reduced.addEventListener('change',()=>{syncSettings();if(context?.kind!=='entrance')arm();});
 syncSettings();
 return {sync(next){const changed=context?.key!==next.key;context=next;if(changed)arm(false,next.kind,true);if(lastLanguage!==language())syncSettings();},restart(manual=false,kind){if(context?.kind==='entrance'&&!kind)return;return arm(manual,kind||context?.kind);},cancel(){cancel();phase='idle';publish();}};
}
