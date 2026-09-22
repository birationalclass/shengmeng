import {createOfflineMusic} from './music-offline.mjs?v=offline1';
export const MUSIC_KEY='group-sudoku-music-v1';
export function musicPreferences(storage){
 let value;try{value=JSON.parse(storage?.getItem(MUSIC_KEY)||'null');}catch{}
 return {enabled:typeof value?.enabled==='boolean'?value.enabled:true,volume:typeof value?.volume==='number'&&Number.isFinite(value.volume)?Math.max(0,Math.min(1,value.volume)):.12};
}
export function createBackgroundMusic({storage,t}){
 const audio=document.getElementById('backgroundMusic'),toggle=document.getElementById('musicEnabled'),slider=document.getElementById('musicVolume'),output=document.getElementById('musicVolumeValue'),note=document.getElementById('musicStatus');
 const prefs=musicPreferences(storage),testMuted=new URLSearchParams(location.search).get('mute')==='1';let context,gain,source,analyser,wave,spectrum,attempt=0,started=false,pending=false,failed=false,buffering=false,watchdog=0,resumeAt=0;
 const trackUrl=new URL('./audio/magic-study.mp3?stream=offline1',import.meta.url).href;
 audio.crossOrigin='anonymous';audio.loop=true;audio.preload='metadata';audio.volume=prefs.volume;audio.muted=testMuted;
 // Keep the URL on the media element: byte-range buffering stays browser-managed.
 // Never fetch the full track into a Blob or decode it into a JavaScript audio buffer.
 function attach(){if(!audio.getAttribute('src')){audio.preload='metadata';audio.src=trackUrl;audio.load();}else if(audio.error)audio.load();}
 function clearWatch(){clearTimeout(watchdog);watchdog=0;}
 function release(){attempt++;pending=false;buffering=false;clearWatch();if(audio.getAttribute('src')&&Number.isFinite(audio.currentTime))resumeAt=audio.currentTime;audio.pause();audio.removeAttribute('src');audio.load();context?.suspend().catch(()=>{});}
 function watch(){if(watchdog)return;watchdog=setTimeout(()=>{watchdog=0;release();failed=true;sync();},20000);}
 function save(){try{storage?.setItem(MUSIC_KEY,JSON.stringify(prefs));}catch{}}
 function sync(){
  toggle.checked=prefs.enabled;slider.value=String(Math.round(prefs.volume*100));output.value=slider.value+'%';slider.setAttribute('aria-valuetext',output.value);
  document.getElementById('musicTitle').textContent=t('背景音乐','Background music');document.getElementById('musicToggleLabel').textContent=t('循环播放','Loop playback');document.getElementById('musicVolumeLabel').textContent=t('音量','Volume');
  note.textContent=!prefs.enabled?t('音乐已关闭','Music off'):failed?t('音乐加载中断，轻触页面重试。','Music loading interrupted. Tap the page to retry.'):prefs.volume===0?t('已静音','Muted'):!started?t('轻触页面或按键后，音乐轻声响起。','Tap the page or press a key to start softly.'):pending||buffering?t('正在缓冲音乐，稍后继续播放…','Buffering music; playback will resume…'):t('哈利波特 · 专注学习歌单','Harry Potter · Study playlist');
 }
 function applyVolume(){
  if(gain){gain.gain.cancelScheduledValues(context.currentTime);gain.gain.setTargetAtTime(prefs.enabled&&!testMuted?prefs.volume:0,context.currentTime,.06);audio.volume=1;}else audio.volume=prefs.enabled&&!testMuted?prefs.volume:0;
 }
 function ensureGraph(){
  if(context)return;const AudioContext=window.AudioContext||window.webkitAudioContext;if(!AudioContext)return;
  // GainNode also controls volume on iOS, where HTMLMediaElement.volume can be ignored.
  try{context=new AudioContext();gain=context.createGain();gain.gain.value=prefs.enabled&&!testMuted?prefs.volume:0;source=context.createMediaElementSource(audio);analyser=context.createAnalyser();analyser.fftSize=512;analyser.smoothingTimeConstant=.7;wave=new Float32Array(analyser.fftSize);spectrum=new Uint8Array(analyser.frequencyBinCount);source.connect(analyser);analyser.connect(gain);gain.connect(context.destination);audio.volume=1;}catch{context?.close().catch(()=>{});context=null;gain=null;audio.volume=prefs.volume;}
 }
 async function start(){
  if(!prefs.enabled||prefs.volume===0||document.hidden||pending)return;
  if(!audio.paused&&(!context||context.state==='running')&&!failed)return;
  const token=++attempt;failed=false;started=true;pending=true;ensureGraph();applyVolume();attach();
  sync();watch();
  try{const resume=context?.resume();const play=audio.play();await Promise.all([resume,play]);if(token!==attempt)return;if(!prefs.enabled||prefs.volume===0){audio.pause();return;}failed=false;buffering=false;clearWatch();}
  catch(error){if(token!==attempt)return;clearWatch();if(error.name==='NotAllowedError')started=false;else if(error.name!=='AbortError')failed=true;}
  finally{if(token===attempt){pending=false;sync();}}
 }
 function gesture(e){if(e.target.closest?.('.music-settings')||e.ctrlKey||e.metaKey||e.altKey||e.repeat)return;if(prefs.enabled&&(failed||audio.paused||context?.state==='suspended'))void start();}
 document.addEventListener('pointerdown',gesture,{capture:true,passive:true});document.addEventListener('keydown',gesture,true);document.addEventListener('click',gesture,true);
 toggle.addEventListener('change',()=>{prefs.enabled=toggle.checked;save();if(!prefs.enabled){release();applyVolume();sync();}else void start();});
 slider.addEventListener('input',()=>{prefs.volume=Math.max(0,Math.min(100,Number(slider.value)))/100;applyVolume();save();if(prefs.volume===0)release();sync();if(prefs.enabled&&prefs.volume>0)void start();});
 audio.addEventListener('loadedmetadata',()=>{if(resumeAt>0){const target=resumeAt;resumeAt=0;try{audio.currentTime=target;}catch{}}});
 audio.addEventListener('error',()=>{clearWatch();attempt++;pending=false;buffering=false;failed=true;sync();});
 audio.addEventListener('playing',()=>{clearWatch();pending=false;buffering=false;failed=false;sync();});
 for(const event of ['waiting','stalled'])audio.addEventListener(event,()=>{if(!prefs.enabled||audio.paused||(event==='stalled'&&audio.readyState>=3))return;buffering=true;watch();sync();});
 audio.addEventListener('timeupdate',()=>{if(buffering&&!audio.paused&&audio.readyState>=3){buffering=false;clearWatch();sync();}});
 window.addEventListener('music-cache-change',()=>{const playing=started&&!audio.paused;release();if(playing)void start();else if(prefs.enabled&&prefs.volume>0)attach();});
 window.addEventListener('pagehide',release);window.addEventListener('pageshow',()=>{if(started&&prefs.enabled)void start();});
 // Warm only metadata before the first gesture, not the 43-minute soundtrack.
 if(prefs.enabled&&prefs.volume>0)attach();
 const levels={energy:0,bass:0};
 function readLevels(dt=.016){let energy=0,bass=0;
  if(analyser&&prefs.enabled&&prefs.volume>0&&!audio.paused&&context?.state==='running'){
   analyser.getFloatTimeDomainData(wave);analyser.getByteFrequencyData(spectrum);
   const raw=analyseMusic(wave,spectrum,context.sampleRate);energy=raw.energy;bass=raw.bass;
  }
  for(const key of ['energy','bass']){const value=key==='energy'?energy:bass;const rate=value>levels[key]?10:2.5;levels[key]+=(value-levels[key])*(1-Math.exp(-Math.max(0,dt)*rate));}return levels;
 }
 window.addEventListener('course-language',sync);sync();createOfflineMusic({t});return {sync,readLevels};
}

export function analyseMusic(wave,spectrum,sampleRate=48000){let sum=0;for(const v of wave)sum+=v*v;const rms=Math.sqrt(sum/Math.max(1,wave.length));let bass=0,count=0;for(let i=1;i<spectrum.length;i++){const hz=i*sampleRate/(spectrum.length*2);if(hz>320)break;if(hz>=45){bass+=spectrum[i]/255;count++;}}return {energy:Math.min(1,rms*4.5),bass:count?bass/count:0};}
