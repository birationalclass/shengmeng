/* Automatic original dialogue; the only preference is whether narration repeats.
 * Same-origin excerpt, with volume 80%; background music is never ducked.
 */
(() => {
  'use strict';
  const panel=document.getElementById('openingSettings'),dialog=document.getElementById('courseOpening');
  const loop=panel.querySelector('[data-voice-loop]');
  const audio=new Audio(new URL('./audio/gandalf-ring-verse-valley.mp3',document.baseURI).href);audio.preload='auto';audio.volume=.8;
  const loopPreference='courseOpeningVoiceLoop.v1';
  loop.checked=false;try{loop.checked=localStorage.getItem(loopPreference)==='true';}catch(_){}
  let visible=false,played=false,request=0,active=false,unlocked=false,cycle=0,playedCycle=null;
  const state=()=>dialog.dataset.voiceState=active?'playing':'idle';
  function pause(){request++;active=false;audio.pause();audio.muted=false;state();}
  function stop(){pause();visible=false;played=false;playedCycle=null;cycle=0;audio.currentTime=0;}
  async function unlock(){
    if(unlocked||active)return;
    const version=++request;audio.muted=true;
    try{await audio.play();unlocked=true;}catch(_){}
    if(version===request){audio.pause();audio.currentTime=0;audio.muted=false;}
  }
  async function play(){
    if(!dialog.open||document.hidden)return;
    pause();const version=++request;active=true;played=true;playedCycle=cycle;audio.currentTime=0;state();
    try{await audio.play();if(version!==request){if(!active)audio.pause();return;}unlocked=true;}
    catch(error){if(version!==request)return;active=false;state();dialog.dataset.voiceState=error.name==='NotAllowedError'?'blocked':'error';}
  }
  function save(){try{localStorage.setItem(loopPreference,String(loop.checked));}catch(_){}}
  loop.addEventListener('change',save);
  panel.querySelector('[data-settings-reset]').addEventListener('click',()=>{stop();loop.checked=false;save();});
  audio.addEventListener('loadedmetadata',()=>{dialog.dataset.voiceDuration=audio.duration.toFixed(3);});
  audio.addEventListener('ended',()=>{active=false;state();});
  audio.addEventListener('error',()=>{pause();dialog.dataset.voiceState='error';});
  document.addEventListener('visibilitychange',()=>{if(document.hidden)pause();});
  dialog.addEventListener('close',stop);window.addEventListener('pagehide',stop);
  window.CourseOpeningVoice={stop,unlock,holdsScene:()=>active,scene(index,shown,direction,currentCycle=0,englishVisible=true){
    cycle=currentCycle;
    const next=index===5&&shown&&direction>0;
    if(!next&&visible)pause();
    const entered=next&&!visible;visible=next;
    if(next&&!active&&englishVisible&&(!played||(loop.checked&&(entered||cycle!==playedCycle))))play();
  }};
})();
