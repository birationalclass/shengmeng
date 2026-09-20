export const MUSIC_KEY='group-sudoku-music-v1';
export function musicPreferences(storage){
 let value;try{value=JSON.parse(storage?.getItem(MUSIC_KEY)||'null');}catch{}
 return {enabled:typeof value?.enabled==='boolean'?value.enabled:true,volume:typeof value?.volume==='number'&&Number.isFinite(value.volume)?Math.max(0,Math.min(1,value.volume)):.12};
}
export function createBackgroundMusic({storage,t}){
 const audio=document.getElementById('backgroundMusic'),toggle=document.getElementById('musicEnabled'),slider=document.getElementById('musicVolume'),output=document.getElementById('musicVolumeValue'),note=document.getElementById('musicStatus');
 const prefs=musicPreferences(storage);let context,gain,source,analyser,wave,spectrum,attempt=0,started=false,pending=false,failed=false;
 audio.loop=true;audio.preload='none';audio.volume=prefs.volume;
 function save(){try{storage?.setItem(MUSIC_KEY,JSON.stringify(prefs));}catch{}}
 function sync(){
  toggle.checked=prefs.enabled;slider.value=String(Math.round(prefs.volume*100));output.value=slider.value+'%';slider.setAttribute('aria-valuetext',output.value);
  document.getElementById('musicTitle').textContent=t('背景音乐','Background music');document.getElementById('musicToggleLabel').textContent=t('循环播放','Loop playback');document.getElementById('musicVolumeLabel').textContent=t('音量','Volume');
  note.textContent=!prefs.enabled?t('音乐已关闭','Music off'):failed?t('音乐暂不可用，可关闭后重新开启。','Music unavailable. Toggle off and on to retry.'):prefs.volume===0?t('已静音','Muted'):!started?t('轻触页面或按键后，音乐轻声响起。','Tap the page or press a key to start softly.'):pending?t('正在加载音乐…','Loading music…'):t('哈利波特 · 专注学习歌单','Harry Potter · Study playlist');
 }
 function applyVolume(){
  if(gain){gain.gain.cancelScheduledValues(context.currentTime);gain.gain.setTargetAtTime(prefs.enabled?prefs.volume:0,context.currentTime,.06);audio.volume=1;}else audio.volume=prefs.enabled?prefs.volume:0;
 }
 function ensureGraph(){
  if(context)return;const AudioContext=window.AudioContext||window.webkitAudioContext;if(!AudioContext)return;
  // GainNode also controls volume on iOS, where HTMLMediaElement.volume can be ignored.
  try{context=new AudioContext();gain=context.createGain();gain.gain.value=prefs.enabled?prefs.volume:0;source=context.createMediaElementSource(audio);analyser=context.createAnalyser();analyser.fftSize=512;analyser.smoothingTimeConstant=.7;wave=new Float32Array(analyser.fftSize);spectrum=new Uint8Array(analyser.frequencyBinCount);source.connect(analyser);analyser.connect(gain);gain.connect(context.destination);audio.volume=1;}catch{context?.close().catch(()=>{});context=null;gain=null;audio.volume=prefs.volume;}
 }
 async function start(){
  if(!prefs.enabled||document.hidden||pending)return;
  const token=++attempt;failed=false;started=true;pending=true;ensureGraph();applyVolume();
  if(!audio.getAttribute('src'))audio.src=new URL('./audio/magic-study.mp3',import.meta.url).href;
  sync();
  try{const resume=context?.resume();const play=audio.play();await Promise.all([resume,play]);if(token!==attempt)return;if(!prefs.enabled){audio.pause();return;}failed=false;}
  catch(error){if(token!==attempt)return;if(error.name==='NotAllowedError')started=false;else if(error.name!=='AbortError')failed=true;}
  finally{if(token===attempt){pending=false;sync();}}
 }
 function gesture(e){if(e.target.closest?.('.music-settings')||e.ctrlKey||e.metaKey||e.altKey||e.repeat)return;if(prefs.enabled&&(audio.paused||context?.state==='suspended'))void start();}
 document.addEventListener('pointerdown',gesture,{capture:true,passive:true});document.addEventListener('keydown',gesture,true);document.addEventListener('click',gesture,true);
 toggle.addEventListener('change',()=>{prefs.enabled=toggle.checked;save();if(!prefs.enabled){attempt++;pending=false;audio.pause();applyVolume();sync();}else void start();});
 slider.addEventListener('input',()=>{prefs.volume=Math.max(0,Math.min(100,Number(slider.value)))/100;applyVolume();save();sync();if(prefs.enabled)void start();});
 audio.addEventListener('error',()=>{pending=false;failed=true;sync();});audio.addEventListener('playing',()=>{pending=false;sync();});
 window.addEventListener('pagehide',()=>{attempt++;pending=false;audio.pause();});window.addEventListener('pageshow',()=>{if(started&&prefs.enabled)void start();});
 const levels={energy:0,bass:0};
 function readLevels(dt=.016){let energy=0,bass=0;
  if(analyser&&prefs.enabled&&prefs.volume>0&&!audio.paused&&context?.state==='running'){
   analyser.getFloatTimeDomainData(wave);analyser.getByteFrequencyData(spectrum);
   const raw=analyseMusic(wave,spectrum,context.sampleRate);energy=raw.energy;bass=raw.bass;
  }
  for(const key of ['energy','bass']){const value=key==='energy'?energy:bass;const rate=value>levels[key]?10:2.5;levels[key]+=(value-levels[key])*(1-Math.exp(-Math.max(0,dt)*rate));}return levels;
 }
 window.addEventListener('course-language',sync);sync();return {sync,readLevels};
}

export function analyseMusic(wave,spectrum,sampleRate=48000){let sum=0;for(const v of wave)sum+=v*v;const rms=Math.sqrt(sum/Math.max(1,wave.length));let bass=0,count=0;for(let i=1;i<spectrum.length;i++){const hz=i*sampleRate/(spectrum.length*2);if(hz>320)break;if(hz>=45){bass+=spectrum[i]/255;count++;}}return {energy:Math.min(1,rms*4.5),bass:count?bass/count:0};}
