/* A user-supplied original recording; never synthesize or substitute a voice. */
(() => {
  'use strict';
  const panel=document.getElementById('openingSettings'),dialog=document.getElementById('courseOpening');
  const enabled=panel.querySelector('[data-voice-enabled]'),file=panel.querySelector('[data-voice-file]'),status=panel.querySelector('[data-voice-status]'),button=panel.querySelector('[data-voice-play]');
  const audio=new Audio();audio.preload='metadata';audio.volume=.9;
  let url='',visible=false,played=false,request=0,active=false;
  function duck(value){window.CourseOpeningAudio?.setDucked(value);}
  function pause(){request++;if(active)status.textContent='原声已暂停';active=false;audio.pause();duck(false);}
  function stop(){pause();visible=false;played=false;audio.currentTime=0;}
  async function play(){
    if(!url||!enabled.checked||!dialog.open||document.hidden)return;
    const version=++request;active=true;
    try{audio.currentTime=0;await audio.play();if(version!==request){if(!active)audio.pause();return;}played=true;duck(true);status.textContent='正在播放原声';}
    catch(error){if(version!==request)return;active=false;duck(false);status.textContent=error.name==='NotAllowedError'?'点击“播放原声”开启声音。':'该音频无法播放，请选择其他音频文件。';}
  }
  file.addEventListener('change',()=>{
    const selected=file.files?.[0];if(!selected)return;
    pause();if(url)URL.revokeObjectURL(url);url=URL.createObjectURL(selected);audio.src=url;
    enabled.checked=true;played=false;button.hidden=false;status.textContent='已选择：'+selected.name+'。环的说明出现时播放。';
    if(visible)play();
  });
  enabled.addEventListener('change',()=>{if(!enabled.checked)pause();else if(visible)play();});
  button.addEventListener('click',play);
  panel.querySelector('[data-settings-reset]').addEventListener('click',()=>{stop();enabled.checked=false;status.textContent=url?'已保留所选音频，原声已关闭。':'选择电影原声音频，在环的说明出现时播放。文件仅在本次浏览中使用。';});
  audio.addEventListener('ended',()=>{active=false;duck(false);status.textContent='原声播放完毕';});
  audio.addEventListener('error',()=>{pause();status.textContent='该音频无法播放，请选择其他音频文件。';});
  document.addEventListener('visibilitychange',()=>{if(document.hidden)pause();});
  dialog.addEventListener('close',stop);window.addEventListener('pagehide',stop);
  window.CourseOpeningVoice={stop,scene(index,shown,direction){
    const next=index===5&&shown&&direction>0;
    if(!next&&visible){pause();played=false;}
    const entered=next&&!visible;visible=next;
    if(entered&&!played&&enabled.checked)play();
  }};
})();
