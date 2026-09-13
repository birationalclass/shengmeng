/* User-selected Bilibili source through its official external player.
 * A locally selected audio file can replace the embed for the current visit.
 * Player parameters: https://player.bilibili.com/
 */
(() => {
  'use strict';
  const panel=document.getElementById('openingSettings'),dialog=document.getElementById('courseOpening');
  const enabled=panel.querySelector('[data-voice-enabled]'),file=panel.querySelector('[data-voice-file]'),status=panel.querySelector('[data-voice-status]'),button=panel.querySelector('[data-voice-play]');
  const trigger=dialog.querySelector('[data-voice-open]'),clip=dialog.querySelector('.opening-clip'),mount=dialog.querySelector('[data-clip-mount]');
  const audio=new Audio();audio.preload='metadata';audio.volume=.9;
  let url='',visible=false,played=false,request=0,active=false;
  const ready='已接入 B 站铭文片段。开启后随环场景显示播放器；关闭播放器继续动画。也可选择本地音频。';
  function duck(value){window.CourseOpeningAudio?.setDucked(value);}
  function pause(){request++;if(active)status.textContent='原声已暂停';active=false;audio.pause();mount.replaceChildren();clip.hidden=true;duck(false);}
  function stop(){pause();visible=false;played=false;trigger.hidden=true;audio.currentTime=0;}
  async function play(){
    if(!enabled.checked||!dialog.open||document.hidden)return;
    pause();const version=++request;active=true;played=true;
    if(!url){
      const frame=document.createElement('iframe');
      frame.title='One ring to rule them all — B 站原声';
      frame.src='https://player.bilibili.com/player.html?bvid=BV1xL4y1u7xZ&p=1&autoplay=1&danmaku=0';
      frame.allow='autoplay; fullscreen';frame.allowFullscreen=true;frame.referrerPolicy='strict-origin-when-cross-origin';
      mount.replaceChildren(frame);clip.hidden=false;duck(true);status.textContent='B 站播放器已打开；关闭后继续动画。';return;
    }
    try{audio.currentTime=0;await audio.play();if(version!==request){if(!active)audio.pause();return;}duck(true);status.textContent='正在播放本地原声';}
    catch(error){if(version!==request)return;active=false;duck(false);status.textContent=error.name==='NotAllowedError'?'点击“播放原声”开启声音。':'该音频无法播放，请选择其他音频文件。';}
  }
  function manualPlay(){enabled.checked=true;play();}
  file.addEventListener('change',()=>{
    const selected=file.files?.[0];if(!selected)return;
    pause();if(url)URL.revokeObjectURL(url);url=URL.createObjectURL(selected);audio.src=url;
    enabled.checked=true;played=false;status.textContent='已选择：'+selected.name+'。环的说明出现时播放。';
    if(visible)play();
  });
  enabled.addEventListener('change',()=>{if(!enabled.checked)pause();else if(visible)play();});
  button.addEventListener('click',manualPlay);trigger.addEventListener('click',manualPlay);
  dialog.querySelector('[data-clip-close]').addEventListener('click',()=>{pause();trigger.focus({preventScroll:true});});
  panel.querySelector('[data-settings-reset]').addEventListener('click',()=>{stop();enabled.checked=false;status.textContent=url?'已保留本地音频，原声已关闭。':ready;});
  audio.addEventListener('ended',()=>{active=false;duck(false);status.textContent='原声播放完毕';});
  audio.addEventListener('error',()=>{pause();status.textContent='该音频无法播放，请选择其他音频文件。';});
  document.addEventListener('visibilitychange',()=>{if(document.hidden)pause();});
  dialog.addEventListener('close',stop);window.addEventListener('pagehide',stop);
  window.CourseOpeningVoice={stop,holdsScene:()=>active,scene(index,shown,direction){
    const next=index===5&&shown&&direction>0;
    trigger.hidden=!next;
    if(!next&&visible){pause();played=false;}
    const entered=next&&!visible;visible=next;
    if(entered&&!played&&enabled.checked)play();
  }};
})();
