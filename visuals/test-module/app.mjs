import {setupMusic} from './music.mjs?v=20260920audio2';
import {AtlasScene} from './scene.mjs?v=20260920h';
import {DURATION,PHASES,phaseAt,clamp} from './story.mjs?v=20260920h';
const $=id=>document.getElementById(id),canvas=$('world');
const defaults={speed:1,quality:'standard',captions:false,timeline:false,dust:true,loop:false,reduced:matchMedia('(prefers-reduced-motion: reduce)').matches};
let prefs={...defaults};try{const saved=JSON.parse(localStorage.getItem('operations-atlas-v2')||'{}');for(const k of Object.keys(defaults))if(typeof saved[k]===typeof defaults[k])prefs[k]=saved[k];}catch{}
if(!['standard','high','low'].includes(prefs.quality))prefs.quality='standard';if(![.65,1,1.5].includes(prefs.speed))prefs.speed=1;
let music;let after=0;let entered=false;let scene,t=0,playing=false,last=0,phase=null,captionTimer,frame=0,failed=false,dirty=true;
const save=()=>{try{localStorage.setItem('operations-atlas-v2',JSON.stringify(prefs));}catch{}};
const clock=n=>`${String(Math.floor(n/60)).padStart(2,'0')}:${String(Math.floor(n%60)).padStart(2,'0')}`;
function setPlaying(value){playing=value&&!failed&&entered;$('play').textContent=playing?'Ⅱ':'▷';$('play').setAttribute('aria-label',playing?'暂停动画':'播放动画');$('cinema').dataset.playing=String(playing);last=0;music?.sync();}
function caption(p){$('era').textContent=p.era;$('englishTitle').textContent=p.en;$('chineseTitle').textContent=p.zh;$('narration').textContent=p.line;$('englishNarration').textContent=p.sub;$('formula').textContent=p.formula;const n=PHASES.indexOf(p);$('sceneNumber').textContent=n===0?'PROLOGUE':n===PHASES.length-1?'CODA':`CHAPTER 0${n}`;const actions={semigroup:'让字母相连 ↗',remainder:'观看木塔搭建 ↗',action:'看苹果下落 ↗',permutation:'观看根的置换 ↗',symmetry:'观看晶格展开 ↗',composition:'沿着计算前进 ↗',epilogue:'重看序曲 ↗'};$('sceneAction').hidden=!actions[p.id];$('sceneAction').textContent=actions[p.id]||'';document.querySelector('.titles').classList.remove('changing');}
function sync(immediate=false){const p=phaseAt(t);$('seek').value=t;$('seek').style.setProperty('--progress',`${t/DURATION*100}%`);$('time').textContent=`${clock(t)} / ${clock(DURATION)}`;$('cinema').dataset.time=t.toFixed(2);$('cinema').dataset.phase=p.id;
 if(p!==phase||immediate){clearTimeout(captionTimer);phase=p;for(const b of document.querySelectorAll('[data-time]')){if(Number(b.dataset.time)===p.start)b.setAttribute('aria-current','step');else b.removeAttribute('aria-current');}if(immediate||prefs.reduced)caption(p);else{document.querySelector('.titles').classList.add('changing');captionTimer=setTimeout(()=>caption(p),500);}}
}
function automatic(){if(scene)scene.manual=null;document.body.classList.remove('manual');$('returnCamera').hidden=true;$('viewHint').textContent='镜头自动巡游 · 拖动可自由观察';dirty=true;}
function jump(value,play=false){after=0;document.body.classList.remove('touring');$('replay').hidden=true;t=clamp(value,0,DURATION);music?.seek();automatic();sync(true);dirty=true;if(play)setPlaying(true);}
function manual(){document.body.classList.add('manual');$('returnCamera').hidden=false;$('viewHint').textContent='自由观察 · 拖动旋转 / 滚轮缩放';dirty=true;}
function openNotes(){if(!$('notes').open)$('notes').showModal();const article=$(`note-${phaseAt(t).id}`);if(article)requestAnimationFrame(()=>article.scrollIntoView({block:'start',behavior:'instant'}));else $('notes').scrollTop=0;}
$('notesOpen').onclick=$('notesShortcut').onclick=$('fallbackNotes').onclick=openNotes;
$('settingsOpen').onclick=()=>$('settings').showModal();
for(const b of document.querySelectorAll('[data-close]'))b.onclick=()=>$(b.dataset.close).close();
for(const d of document.querySelectorAll('dialog'))d.addEventListener('click',e=>{if(e.target===d){const b=d.getBoundingClientRect();if(e.clientX<b.left||e.clientX>b.right||e.clientY<b.top||e.clientY>b.bottom)d.close();}});
$('play').onclick=()=>{if(t>=DURATION)jump(0);setPlaying(!playing);};$('restart').onclick=()=>jump(0,true);$('replay').onclick=()=>jump(0,true);$('seek').oninput=e=>jump(Number(e.target.value));
for(const b of document.querySelectorAll('[data-time]'))b.onclick=()=>jump(Number(b.dataset.time),!prefs.reduced);
$('sceneAction').onclick=()=>jump({semigroup:24,remainder:40,action:84,permutation:108,symmetry:133,composition:169,epilogue:0}[phaseAt(t).id]??0,true);
$('returnCamera').onclick=automatic;
$('fullscreen').onclick=async()=>{try{if(document.fullscreenElement)await document.exitFullscreen();else await $('cinema').requestFullscreen();}catch{$('viewHint').textContent='当前浏览器不支持全屏，可在窗口中继续观看。';}};
function applyPrefs(){for(const key of Object.keys(defaults)){const el=$(key);if(el.type==='checkbox')el.checked=prefs[key];else el.value=prefs[key];}document.body.classList.toggle('no-captions',!prefs.captions);document.body.classList.toggle('no-timeline',!prefs.timeline);if(scene){scene.dust.visible=prefs.dust;scene.setQuality(prefs.quality);}dirty=true;}
for(const key of Object.keys(defaults))$(key).addEventListener('change',e=>{prefs[key]=e.target.type==='checkbox'?e.target.checked:key==='speed'?Number(e.target.value):e.target.value;if(key==='reduced'&&prefs.reduced)setPlaying(false);applyPrefs();save();});
let pointer=null;
canvas.addEventListener('pointerdown',e=>{if(e.button!==0||!scene||failed)return;pointer={id:e.pointerId,x:e.clientX,y:e.clientY};canvas.setPointerCapture(e.pointerId);});
canvas.addEventListener('pointermove',e=>{if(!pointer||pointer.id!==e.pointerId||!scene)return;const dx=e.clientX-pointer.x,dy=e.clientY-pointer.y;if(dx||dy){scene.orbit(dx,dy);manual();}pointer.x=e.clientX;pointer.y=e.clientY;});
for(const type of ['pointerup','pointercancel','lostpointercapture'])canvas.addEventListener(type,()=>pointer=null);
canvas.addEventListener('wheel',e=>{if(!scene||failed)return;e.preventDefault();scene.zoom(e.deltaY);manual();},{passive:false});
document.addEventListener('keydown',e=>{if(!entered)return;if(document.querySelector('dialog[open]')||/INPUT|SELECT|TEXTAREA/.test(e.target.tagName))return;if(e.code==='Space'&&e.target.tagName!=='BUTTON'){e.preventDefault();$('play').click();}else if(e.code==='ArrowRight'){e.preventDefault();jump(t+5);}else if(e.code==='ArrowLeft'){e.preventDefault();jump(t-5);}else if(['1','2','3','4','5','6'].includes(e.key)){jump([12,40,70,100,130,160][Number(e.key)-1],!prefs.reduced);}});
window.addEventListener('resize',()=>{scene?.resize();dirty=true;});document.addEventListener('visibilitychange',()=>{last=0;if(document.hidden)music?.audio.pause();else{music?.seek();music?.sync();}});
function fail(error){failed=true;setPlaying(false);$('loading').hidden=true;$('fallback').hidden=false;$('cinema').dataset.ready='fallback';console.error('The mechanical atlas could not render.',error);}
canvas.addEventListener('webglcontextlost',e=>{e.preventDefault();fail('WebGL context lost; reload to restore.');});
function animate(now){if(failed)return;requestAnimationFrame(animate);if(document.hidden){last=0;return;}const dt=last?Math.min((now-last)/1000,.15):0;last=now;
 if(playing){t+=dt*prefs.speed;if(t>=DURATION){if(prefs.loop){t%=DURATION;after=0;document.body.classList.remove('touring');$('replay').hidden=true;}else{after+=dt*prefs.speed;t=DURATION;document.body.classList.add('touring');$('replay').hidden=false;}}sync();}
 if(playing||dirty){scene.update(t+after);dirty=false;frame++;$('cinema').dataset.frames=frame;}
}
music=setupMusic({getPlaying:()=>playing,getTime:()=>t});applyPrefs();sync(true);setPlaying(playing);
try{await Promise.race([document.fonts.ready,new Promise(resolve=>setTimeout(resolve,2000))]);scene=new AtlasScene(canvas,prefs.quality);applyPrefs();scene.update(t);$('cinema').dataset.ready='true';$('loadStatus').textContent='地图已就绪 · 点击进入，开启配乐';$('enterAnimation').hidden=false;$('loading').classList.add('ready');$('enterAnimation').onclick=()=>{if(entered)return;entered=true;$('loading').hidden=true;setPlaying(true);requestAnimationFrame(animate);};}catch(error){fail(error);}
