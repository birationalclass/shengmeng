import {controlLabel} from './control-label.js?v=22-handwritten-cover';

export function createBackgroundMusic({audio,button,volume,readout,events=document,storage,
  requestFrame=requestAnimationFrame,cancelFrame=cancelAnimationFrame,now=()=>performance.now()}){
  try{storage??=globalThis.localStorage;}catch{}
  const read=key=>{try{return storage?.getItem(key)??null;}catch{return null;}};
  const save=(key,value)=>{try{storage?.setItem(key,String(value));}catch{}};
  const savedVolume=read('refuge-music-volume');
  let level=savedVolume===null?.18:Math.max(0,Math.min(1,Number(savedVolume)||0));
  let enabled=read('refuge-music-enabled')!=='false',unlocked=false,pending=false,disposed=false,revision=0,frame=0;
  audio.loop=true;audio.preload='none';audio.volume=0;
  volume.value=String(Math.round(level*100));readout.textContent=volume.value+'%';
  function show(label){
    const active=enabled&&(pending||!audio.paused);
    button.setAttribute('aria-pressed',String(active));
    controlLabel(button,label||(active?'暂停背景音乐':'播放背景音乐'));
  }
  function fade(target,done){
    cancelFrame(frame);const start=now(),from=audio.volume;
    const step=()=>{const t=Math.min(1,(now()-start)/800);audio.volume=from+(target-from)*t*t*(3-2*t);
      if(t<1)frame=requestFrame(step);else{frame=0;done?.();}};
    frame=requestFrame(step);
  }
  function suspend(){revision++;pending=false;cancelFrame(frame);frame=0;audio.pause();audio.volume=0;show();}
  async function play(){
    if(disposed||events.hidden)return;
    unlocked=true;enabled=true;pending=true;const token=++revision;
    cancelFrame(frame);frame=0;
    if(!audio.getAttribute('src'))audio.src=audio.dataset.src;
    show();
    try{await audio.play();if(disposed||token!==revision)return;pending=false;fade(level);show();}
    catch(error){if(token!==revision||disposed)return;pending=false;show(error.name==='NotAllowedError'?'播放背景音乐':'音乐暂未加载，点击重试');}
  }
  function toggle(){
    unlocked=true;
    if(enabled&&(pending||!audio.paused)){
      enabled=false;revision++;pending=false;fade(0,()=>audio.pause());show();
    }else{play();}
    save('refuge-music-enabled',enabled);
  }
  function changeVolume(){
    level=Math.max(0,Math.min(1,Number(volume.value)/100));readout.textContent=Math.round(level*100)+'%';save('refuge-music-volume',level);
    if(enabled&&!audio.paused)fade(level);
  }
  function visibility(){if(events.hidden)suspend();else if(enabled&&unlocked)play();}
  function error(){pending=false;show('音乐暂未加载，点击重试');}
  button.addEventListener('click',toggle);volume.addEventListener('input',changeVolume);
  events.addEventListener('visibilitychange',visibility);
  audio.addEventListener('error',error);show();
  return {start(){save('refuge-music-enabled',true);return play();},dispose(){disposed=true;suspend();button.removeEventListener('click',toggle);volume.removeEventListener('input',changeVolume);
    events.removeEventListener('visibilitychange',visibility);audio.removeEventListener('error',error);}};
}
