/* Short original dialogue excerpt, trimmed from the user-selected source.
 * The scene uses a same-origin audio file; no third-party player is loaded.
 */
(() => {
  'use strict';
  const panel=document.getElementById('openingSettings'),dialog=document.getElementById('courseOpening');
  const loop=panel.querySelector('[data-voice-loop]'),enabled=panel.querySelector('[data-voice-enabled]'),file=panel.querySelector('[data-voice-file]'),status=panel.querySelector('[data-voice-status]'),button=panel.querySelector('[data-voice-play]');
  const source=new URL('./audio/gandalf-ring-verse-valley.mp3',document.baseURI).href;
  const audio=new Audio(source);audio.preload='auto';audio.volume=.8;
  const preference='courseOpeningVoice.v1',loopPreference='courseOpeningVoiceLoop.v1';
  loop.checked=false;try{loop.checked=localStorage.getItem(loopPreference)==='true';}catch(_){}
  enabled.checked=true;try{const saved=localStorage.getItem(preference);if(saved!==null)enabled.checked=saved==='true';}catch(_){}
  let localUrl='',visible=false,played=false,request=0,active=false,unlocked=false,cycle=0,playedCycle=null;
  const ready='每次打开动画，台词原声默认只播放一次；原声结束后继续动画。';
  function controls(){button.textContent=active?'暂停原声':'播放原声';dialog.dataset.voiceState=active?'playing':'idle';}
  function pause(){request++;active=false;audio.pause();audio.muted=false;controls();}
  function stop(){pause();visible=false;played=false;playedCycle=null;cycle=0;audio.currentTime=0;}
  // Prime this same audio element during the user's start gesture. A muted
  // first instant avoids audible dialogue before the ring has appeared.
  async function unlock(){
    if(unlocked||active)return;
    const version=++request;audio.muted=true;
    try{await audio.play();unlocked=true;}catch(_){}
    if(version===request){audio.pause();audio.currentTime=0;audio.muted=false;}
  }
  async function play(){
    if(!enabled.checked||!dialog.open||document.hidden)return;
    pause();const version=++request;active=true;played=true;playedCycle=cycle;audio.currentTime=0;controls();
    try{await audio.play();if(version!==request){if(!active)audio.pause();return;}unlocked=true;status.textContent='正在播放甘道夫原声';}
    catch(error){if(version!==request)return;active=false;controls();status.textContent=error.name==='NotAllowedError'?'点击“播放原声”开启声音。':'原声暂时无法加载，请重试或选择本地音频。';}
  }
  function save(){try{localStorage.setItem(preference,String(enabled.checked));localStorage.setItem(loopPreference,String(loop.checked));}catch(_){}}
  function manualPlay(){if(active){pause();status.textContent='原声已暂停';return;}enabled.checked=true;save();play();}
  file.addEventListener('change',()=>{
    const selected=file.files?.[0];if(!selected)return;
    pause();if(localUrl)URL.revokeObjectURL(localUrl);localUrl=URL.createObjectURL(selected);audio.src=localUrl;
    enabled.checked=true;save();played=false;status.textContent='已选择：'+selected.name+'。环的台词出现时播放。';
    if(visible)play();
  });
  enabled.addEventListener('change',()=>{save();if(!enabled.checked){pause();status.textContent='原声已关闭';}else if(visible)play();else status.textContent=ready;});
  loop.addEventListener('change',()=>{save();status.textContent=loop.checked?'循环播放已开启；下一轮台词出现时重播。':'循环播放已关闭；本次打开动画中，已播放的台词不会自动重播。';});
  button.addEventListener('click',manualPlay);
  panel.querySelector('[data-settings-reset]').addEventListener('click',()=>{stop();if(localUrl){URL.revokeObjectURL(localUrl);localUrl='';}audio.src=source;file.value='';enabled.checked=true;loop.checked=false;save();status.textContent=ready;});
  audio.addEventListener('loadedmetadata',()=>{dialog.dataset.voiceDuration=audio.duration.toFixed(3);});
  audio.addEventListener('ended',()=>{active=false;controls();status.textContent='原声播放完毕';});
  audio.addEventListener('error',()=>{pause();dialog.dataset.voiceState='error';status.textContent='原声暂时无法加载，请重试或选择本地音频。';});
  document.addEventListener('visibilitychange',()=>{if(document.hidden)pause();});
  dialog.addEventListener('close',stop);window.addEventListener('pagehide',stop);
  window.CourseOpeningVoice={stop,unlock,holdsScene:()=>active,scene(index,shown,direction,currentCycle=0){
    cycle=currentCycle;
    const next=index===5&&shown&&direction>0;
    if(!next&&visible)pause();
    const entered=next&&!visible;visible=next;
    // A scene remains marked as played for this opening session. The cycle
    // token also permits repeats when the ring is the only selected figure.
    if(next&&!active&&enabled.checked&&((entered&&!played)||(loop.checked&&(entered||cycle!==playedCycle))))play();
  }};
})();
