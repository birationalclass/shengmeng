import {watchPageActivity} from './page-activity.mjs?v=nebula-70';
import {createOfflineMusic} from './music-offline.mjs?v=nebula-69';
export const PLAYLIST=[{title:'INTERSTELLAR',src:new URL('./audio/interstellar.mp3',import.meta.url).href}];
export function createPlaylistPlayer({audio,storage,onState=()=>{},tracks=PLAYLIST}){
 const key='generators-endless-music';let prefs;try{prefs=JSON.parse(storage.getItem(key)||'null');}catch{}
 let index=Number.isInteger(prefs?.index)?((prefs.index%tracks.length)+tracks.length)%tracks.length:0,enabled=prefs?.enabled!==false,volume=Number.isFinite(prefs?.volume)?Math.max(0,Math.min(1,prefs.volume)):.12;
 let suspended=false,resumeOnFocus=false;let state='ready',request=0,failures=0,pending=false,context,gain;
 audio.loop=false;audio.preload='metadata';audio.volume=volume;
 const save=()=>{try{storage.setItem(key,JSON.stringify({index,enabled,volume}));}catch{}};
 const emit=()=>onState({index,enabled,volume,state,title:tracks[index].title,count:tracks.length});
 function level(){if(gain){gain.gain.setTargetAtTime(enabled?volume:0,context.currentTime,.06);audio.volume=1;}else audio.volume=volume;}
 function attach(){const src=tracks[index].src;if(audio.getAttribute('src')!==src){audio.src=src;audio.load();}}
 async function play(){
  if(suspended||!enabled||volume===0||pending)return;
  if(!audio.paused&&state==='playing')return;
  const own=++request;pending=true;state='loading';emit();attach();
  try{
   const AC=globalThis.AudioContext||globalThis.webkitAudioContext;
   if(!context&&AC){context=new AC();gain=context.createGain();context.createMediaElementSource(audio).connect(gain);gain.connect(context.destination);level();}
   await Promise.all([context?.resume(),audio.play()]);if(own!==request)return;state='playing';failures=0;
  }catch(error){if(own!==request)return;state=error.name==='NotAllowedError'?'ready':'error';}
  finally{if(own===request){pending=false;emit();}}
 }
 function next(delta=1){request++;pending=false;audio.pause();index=((index+delta)%tracks.length+tracks.length)%tracks.length;state='ready';save();attach();emit();if(enabled)void play();}
 audio.addEventListener('ended',()=>next());
 audio.addEventListener('error',()=>{request++;pending=false;state='error';emit();if(enabled&&++failures<tracks.length)next();});
 audio.addEventListener('playing',()=>{state='playing';emit();});
 audio.addEventListener('waiting',()=>{if(enabled){state='loading';emit();}});
 audio.addEventListener('pause',()=>{if(!pending){state='paused';emit();}});
 attach();emit();
 return {play,next,sync:emit,setSuspended(value){if(suspended===value)return;suspended=value;if(value){resumeOnFocus=!audio.paused||pending;request++;pending=false;audio.pause();context?.suspend();}else if(resumeOnFocus&&enabled){resumeOnFocus=false;void play();}},setEnabled(value){enabled=!!value;request++;pending=false;save();if(enabled){failures=0;void play();}else{audio.pause();state='paused';emit();}},setVolume(value){volume=Math.max(0,Math.min(1,value));level();save();emit();if(volume>0&&enabled)void play();},stop(){request++;pending=false;audio.pause();context?.suspend();}};
}
export function createEndlessMusic({storage,t}){
 const $=id=>document.getElementById(id),audio=$('backgroundMusic');audio.muted=new URLSearchParams(location.search).get('mute')==='1';
 $('musicStatus').insertAdjacentHTML('afterend','<div class="playlist-controls" hidden><button id="musicPrevious" type="button">←</button><span id="musicTrackCount"></span><button id="musicNext" type="button">→</button></div>');
 $('musicStatus').insertAdjacentHTML('afterend','<button id="musicDownload" type="button"></button><button id="musicCacheClear" type="button"></button><progress id="musicDownloadProgress" max="100" hidden></progress><p id="musicOfflineStatus" role="status"></p>');createOfflineMusic({t});
 const player=createPlaylistPlayer({audio,storage,onState:s=>{
  $('musicEnabled').checked=s.enabled;$('musicVolume').value=String(Math.round(s.volume*100));$('musicVolumeValue').textContent=Math.round(s.volume*100)+'%';
  $('musicTitle').textContent=t('星际 · 背景音乐','Interstellar · Soundtrack');$('musicToggleLabel').textContent=t('背景音乐循环','Loop soundtrack');$('musicVolumeLabel').textContent=t('音量','Volume');
  $('musicStatus').textContent=s.title+' · '+(s.state==='error'?t('加载失败，点击重试','Load failed; tap to retry'):!s.enabled?t('已暂停','Paused'):s.state==='playing'?t('播放中','Playing'):s.state==='loading'?t('缓冲中','Buffering'):t('轻触页面开始','Tap to start'));
  $('musicTrackCount').textContent=`${s.index+1} / ${s.count}`;$('musicPrevious').setAttribute('aria-label',t('上一首','Previous track'));$('musicNext').setAttribute('aria-label',t('下一首','Next track'));
 }});
 watchPageActivity(active=>player.setSuspended(!active));
 $('musicEnabled').onchange=()=>player.setEnabled($('musicEnabled').checked);$('musicVolume').oninput=()=>player.setVolume(Number($('musicVolume').value)/100);$('musicPrevious').onclick=()=>player.next(-1);$('musicNext').onclick=()=>player.next();
 const gesture=e=>{if(e.target.closest?.('.music-settings')||e.repeat||e.ctrlKey||e.metaKey||e.altKey)return;void player.play();};document.addEventListener('pointerdown',gesture,{capture:true,passive:true});document.addEventListener('keydown',gesture,true);window.addEventListener('pagehide',()=>player.stop());return player;
}
