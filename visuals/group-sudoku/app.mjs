import {BUILD_TIME_KEY,readBuildSeconds,buildSeconds} from './construction.mjs?v=palace-clock2';
import {createBackgroundMusic} from './music.mjs?v=palace-clock2';
import {Campaign,MAP_STYLE_KEY,clearLocalData} from './campaign.mjs?v=palace-clock2';
import {SudokuAtlas,REGIONS} from './atlas.mjs?v=palace-clock2';
import {cameraKey} from './camera-navigation.mjs?v=palace-clock2';
import {THEMES} from './journey.mjs?v=palace-clock2';
const $=id=>document.getElementById(id),model=window.AssociativitySudokuModel,canvas=$('world');
let storage;try{storage=localStorage;}catch{}
const campaign=new Campaign(model,storage);let decorationSeconds=readBuildSeconds(storage);
let selected=campaign.current-2,world,game,playing=false,busy=false,boardState,last=0,time=0,reduced=matchMedia('(prefers-reduced-motion: reduce)').matches,toastTimer,mapStyle='parchment',failed=false;
try{mapStyle=storage?.getItem(MAP_STYLE_KEY)||'parchment';}catch{}
const en=()=>window.CourseLanguage.language==='en',t=(zh,eng)=>en()?eng:zh;
const music=createBackgroundMusic({storage,t});
function notify(message){$('toast').textContent=message;$('toast').hidden=false;clearTimeout(toastTimer);toastTimer=setTimeout(()=>$('toast').hidden=true,4500);}
const cameraKeys=new Set();
function phase(value){cameraKeys.clear();busy=!!value;$('playHUD').inert=busy;$('boardHits').inert=busy;document.body.classList.toggle('travelling',busy);document.body.dataset.phase=value||'playing';$('stagePhase').textContent=value==='bridge'?t('吊桥开启 · 前往下一域','THE BRIDGE OPENS · ONWARD'):value==='assembly'?t('镜头就位 · 建筑升起 · 棋盘展开','ARRIVE · BUILD · REVEAL'):'';}
function sync(){
 $('buildTimeLabel').textContent=t('装饰搭建时长','Scenery build time');$('buildTimeValue').value=decorationSeconds+t(' 秒',' s');$('buildTime').value=decorationSeconds;$('buildTimeNote').textContent=t('不含镜头移动和棋盘升起，下次搭建生效。','Excludes camera travel and board rise. Applies to the next build.');
 const done=campaign.completed,r=REGIONS[selected];$('progress').innerHTML=`${done.length} <span>/ 8</span>`;
 $('skillStatus').textContent=campaign.inverseUnlocked?t('单位 · 逆 · 已解锁','Identity · Inverse · Unlocked'):campaign.identityUnlocked?t('单位已解锁 · 第 4 关解锁逆卡','Identity unlocked · Inverse after level 4'):t('通关 3×3 获得单位元卡','Complete 3×3 to unlock Identity');
 $('gameEyebrow').textContent=`${r.n} × ${r.n} · ${en()?r.en:THEMES[selected].name}`;$('gameTitle').textContent=en()?r.en:r.zh;
 $('regionNav').innerHTML=REGIONS.map((r,i)=>`<button data-region="${i}" ${campaign.canEnter(r.n)?'':'disabled'} aria-current="${selected===i}" class="${done.includes(r.n)?'complete':''}">${r.n}×${r.n}<span>${r.zh}</span></button>`).join('');
 $('pins').innerHTML=REGIONS.map((r,i)=>`<button class="map-pin ${done.includes(r.n)?'complete':''}" data-region="${i}" ${campaign.canEnter(r.n)?'':'disabled'} aria-label="${r.zh} ${r.n}×${r.n}${campaign.canEnter(r.n)?'':' 尚未解锁'}">${r.n}×${r.n}${campaign.canEnter(r.n)?'':' ◇'}</button>`).join('');
 $('overview').textContent=t('全图','Atlas');$('language').textContent=en()?'中文':'EN';$('settingsToggle').textContent=t('设置','Settings');$('motionLabel').textContent=t('减少动态','Reduce motion');$('cameraHelp').textContent=t('↑ N · ↓ S · ← W · → E · 滚轮缩放 · 拖动环绕 · Shift＋方向键选格','↑ N · ↓ S · ← W · → E · Wheel to zoom · Drag to orbit · Shift + arrows select cells');$('motion').checked=reduced;syncFullscreen();
 $('clearLocalData').textContent=t('清除本地记录（Cookie）','Clear local data');$('clearDataNote').textContent=t('重置通关进度、未完成棋局和地图设置，重新从 2×2 开始。','Reset progress, unfinished boards and map settings, then start again at 2×2.');
 $('clearDataTitle').textContent=t('清除本地记录？','Clear local data?');$('clearDataWarning').textContent=t('群数独的通关进度、未完成棋局和地图设置将被删除，并从 2×2 重新开始。此操作无法撤销。','Group Sudoku progress, unfinished boards and map settings will be deleted. You will restart at 2×2. This cannot be undone.');$('cancelClearData').textContent=t('取消','Cancel');$('confirmClearData').textContent=t('确认清除','Clear data');
 $('resume').textContent=done.length===8?t('点击棋盘，重游八域','Select a board to play again'):t(`继续 ${campaign.current}×${campaign.current} →`,`Continue ${campaign.current}×${campaign.current} →`);
 $('viewHint').textContent=playing?t('点击选格 · 数字键落子 · 拖动空地观察','Select a cell · Type a number · Drag the ground to orbit'):t('已通关城邦可重玩 · 逐关开启吊桥','Revisit completed domains · Unlock bridges in order');
 world?.setProgress(done);positionTargets();
}
function positionTargets(){if(!world)return;const rect=canvas.getBoundingClientRect();for(const pin of $('pins').children){const p=world.project(+pin.dataset.region);pin.style.left=p.x*rect.width+'px';pin.style.top=p.y*rect.height+'px';pin.style.visibility=p.visible?'visible':'hidden';}
 if(!playing||!boardState)return;for(const b of $('boardHits').children){const k=+b.dataset.boardCell,p=world.cellProjection(selected,k),q=world.cellProjection(selected,k%boardState.n===boardState.n-1?k-1:k+1),w=Math.max(14,Math.abs(p.x-q.x)*rect.width*.88);b.style.left=p.x*rect.width+'px';b.style.top=p.y*rect.height+'px';b.style.width=w+'px';b.style.height=w*.72+'px';b.style.visibility=p.visible?'visible':'hidden';}}
function renderBoard(state){
 const status=$('gameMount').querySelector('.sudoku-status');if(status&&/^(数字键填数|Number keys to enter)/.test(status.textContent))status.textContent=t('方向键 N/S/W/E 平移 · 滚轮缩放 · Shift＋方向键选格 · 数字键填数','Arrows move N/S/W/E · Wheel to zoom · Shift + arrows select cells · Number keys enter');
 const restore=document.activeElement?.hasAttribute('data-board-cell');boardState=state;world?.paint(selected,state);
 $('boardHits').innerHTML=state.cells.map((cell,k)=>`<button data-board-cell="${k}" aria-label="${cell.label}" aria-pressed="${state.selected===k}" tabindex="${state.selected===k?0:-1}"></button>`).join('');positionTargets();
 if(restore)$('boardHits').querySelector(`[data-board-cell="${state.selected}"]`)?.focus({preventScroll:true});
}
function openGame(index,{replay=false}={}){
 if(busy||!campaign.canEnter(index+2))return;selected=index;playing=true;document.body.classList.add('playing');document.body.classList.remove('touring','previewing');$('playHUD').hidden=false;$('stageTitle').hidden=false;
 if(replay)campaign.save(index+2,model.initial(index+2));sync();game?.destroy();
 game=window.AssociativitySudoku.render($('gameMount'),{level:index+2,values:campaign.board(index+2),completed:campaign.completed,fixedLevel:true,sceneBoard:true,actionSkills:true,requireIdentityUnlock:true,requireInverseUnlock:true,onRender:renderBoard,onChange:(n,v)=>{campaign.save(n,v);sync();if(!busy&&model.inspect(v).kind==='complete'){phase('bridge');queueMicrotask(()=>finish(n));}}});
 if(world){phase('assembly');world.arrive(index,()=>{phase('');sync();},reduced);}else phase('');
}
function finish(n){
 const all=campaign.completed.length===8;world?.setProgress(campaign.completed);notify(n===3?t('三阳开泰 · 单位元卡已解锁','THREEFOLD RENEWAL · IDENTITY UNLOCKED'):n===5?t('五福临门 · 逆技能卡已解锁','FIVE BLESSINGS · INVERSE UNLOCKED'):t(`${REGIONS[n-2].zh} · 通关`,`${REGIONS[n-2].en} · COMPLETE`));
 if(all){phase('');showAtlas(true);return;}
 // Replay never takes away earned bridges or progress.
 if(n<campaign.current-1){phase('');showAtlas();return;}
 const next=campaign.current-2;world?.setProgress(campaign.completed);
 if(world&&n<9)world.cross(n-2,()=>{phase('');openGame(next);},reduced);else{phase('');openGame(next);}
}
function showAtlas(tour=false){if(busy)return;playing=false;game?.destroy();game=null;$('boardHits').innerHTML='';$('playHUD').hidden=true;$('stageTitle').hidden=true;document.body.classList.remove('playing','previewing');document.body.classList.toggle('touring',tour);document.body.dataset.phase=tour?'tour':'atlas';sync();if(tour)world?.startTour();else world?.focus(-1);}
function previewArchitecture(index){
 if(busy||!world)return;selected=index;playing=false;game?.destroy();game=null;$('boardHits').innerHTML='';$('playHUD').hidden=true;$('stageTitle').hidden=false;document.body.classList.remove('playing','touring');document.body.classList.add('previewing');sync();
 // The preview only assembles geometry; it never saves a board or unlocks a level.
 world.resetArchitecture(index);phase('assembly');world.arrive(index,()=>{phase('');document.body.dataset.phase='preview';$('stagePhase').textContent=t('建筑预览 · 不影响通关进度','ARCHITECTURE PREVIEW · PROGRESS UNCHANGED');},reduced);
}
function choose(i){if(!busy&&campaign.canEnter(i+2))openGame(i,{replay:campaign.completed.includes(i+2)});}
for(const id of ['regionNav','pins'])$(id).addEventListener('click',e=>{const b=e.target.closest('[data-region]');if(b&&!b.disabled)choose(+b.dataset.region);});
$('previewArchitecture').onclick=()=>{previewArchitecture(+$('previewRegion').value);$('settingsPanel').hidden=true;$('settingsToggle').setAttribute('aria-expanded','false');};
$('overview').onclick=()=>showAtlas(campaign.completed.length===8);$('resume').onclick=()=>{if(campaign.completed.length!==8)openGame(campaign.current-2);else showAtlas(true);};
$('boardHits').addEventListener('click',e=>{if(busy)return;const b=e.target.closest('[data-board-cell]');if(b){game?.select(+b.dataset.boardCell);$('boardHits').querySelector(`[data-board-cell="${b.dataset.boardCell}"]`)?.focus({preventScroll:true});}});
$('boardHits').addEventListener('keydown',e=>{if(!game||busy)return;if(!e.shiftKey&&['ArrowUp','ArrowDown','ArrowLeft','ArrowRight'].includes(e.key))return;const n=boardState.n,offset={ArrowLeft:-1,ArrowRight:1,ArrowUp:-n,ArrowDown:n}[e.key];if(offset){e.preventDefault();game.select((boardState.selected+offset+n*n)%(n*n));$('boardHits').querySelector(`[data-board-cell="${boardState.selected}"]`)?.focus({preventScroll:true});}else if(/^[1-9]$/.test(e.key)&&+e.key<=n){e.preventDefault();game.enter(+e.key);}else if(['Delete','Backspace'].includes(e.key)){e.preventDefault();game.enter(0);}});
document.addEventListener('keydown',e=>{if(!playing||busy||!game||e.defaultPrevented||e.target.closest('#boardHits,#settingsPanel,#clearDataDialog,input,textarea,select'))return;if(/^[1-9]$/.test(e.key)&&+e.key<=boardState.n){e.preventDefault();game.enter(+e.key);}else if(e.key==='Backspace'||e.key==='Delete'){e.preventDefault();game.enter(0);}});
// Capture before focused board cells or buttons can interpret the arrow keys.
function clearCameraKeys(){cameraKeys.clear();}
document.addEventListener('keydown',e=>{if(!cameraKey(e)||e.target.closest('input,textarea,select,[contenteditable=true],#settingsPanel,#clearDataDialog')||!world||busy)return;e.preventDefault();e.stopImmediatePropagation();cameraKeys.add(e.key);world.touring=false;},true);
document.addEventListener('keyup',e=>cameraKeys.delete(e.key),true);
window.addEventListener('blur',clearCameraKeys);document.addEventListener('visibilitychange',clearCameraKeys);
$('settingsToggle').onclick=()=>{$('settingsPanel').hidden=!$('settingsPanel').hidden;$('settingsToggle').setAttribute('aria-expanded',String(!$('settingsPanel').hidden));};
$('clearLocalData').onclick=()=>{$('clearDataDialog').showModal();$('cancelClearData').focus();};
$('cancelClearData').onclick=()=>$('clearDataDialog').close();
$('confirmClearData').onclick=()=>{try{clearLocalData(storage);window.location.reload();}catch{$('clearDataDialog').close();notify(t('无法清除本地记录，请检查浏览器的存储权限。','Unable to clear local data. Please check browser storage permissions.'));}};
for(const input of document.querySelectorAll('[name="mapStyle"]')){input.checked=input.value===mapStyle;input.addEventListener('change',()=>{mapStyle=input.value;world?.setMapStyle(mapStyle);try{storage?.setItem(MAP_STYLE_KEY,mapStyle);}catch{}});}
$('language').onclick=()=>{window.CourseLanguage.language=en()?'zh':'en';document.documentElement.lang=en()?'en':'zh-CN';window.dispatchEvent(new Event('course-language'));sync();};
$('buildTime').oninput=()=>{decorationSeconds=buildSeconds($('buildTime').value);if(world)world.decorationSeconds=decorationSeconds;try{storage?.setItem(BUILD_TIME_KEY,String(decorationSeconds));}catch{}sync();};
$('motion').onchange=()=>{reduced=$('motion').checked;sync();};
function fullscreenElement(){return document.fullscreenElement||document.webkitFullscreenElement;}
function syncFullscreen(){const active=!!fullscreenElement();document.documentElement.classList.toggle('is-fullscreen',active);$('fullscreen').setAttribute('aria-pressed',String(active));$('fullscreen').setAttribute('aria-label',active?t('退出全屏','Exit fullscreen'):t('全屏','Fullscreen'));}
$('fullscreen').onclick=async()=>{const button=$('fullscreen');if(button.disabled)return;button.disabled=true;try{if(fullscreenElement()){const exit=document.exitFullscreen||document.webkitExitFullscreen;await exit.call(document);}else{const root=document.documentElement,enter=root.requestFullscreen||root.webkitRequestFullscreen;if(!enter)throw Error('unsupported');await enter.call(root);}}catch{notify(t('当前窗口不支持全屏','Fullscreen unavailable'));}finally{button.disabled=false;syncFullscreen();scheduleLayout();}};
let pointer=null;
canvas.addEventListener('pointerdown',e=>{if(e.button!==0||!world||busy)return;world.touring=false;pointer={id:e.pointerId,x:e.clientX,y:e.clientY,startX:e.clientX,startY:e.clientY,moved:false};canvas.setPointerCapture(e.pointerId);});
canvas.addEventListener('pointermove',e=>{if(!pointer||!world)return;const dx=e.clientX-pointer.x,dy=e.clientY-pointer.y;if(Math.hypot(e.clientX-pointer.startX,e.clientY-pointer.startY)>4)pointer.moved=true;if(pointer.moved)world.orbit(dx,dy);pointer.x=e.clientX;pointer.y=e.clientY;});
canvas.addEventListener('pointerup',e=>{if(pointer&&!pointer.moved&&world&&!playing){const r=canvas.getBoundingClientRect(),hit=world.pick((e.clientX-r.left)/r.width*2-1,1-(e.clientY-r.top)/r.height*2);if(hit>=0)choose(hit);}pointer=null;});canvas.addEventListener('pointercancel',()=>pointer=null);canvas.addEventListener('lostpointercapture',()=>pointer=null);
canvas.addEventListener('wheel',e=>{if(!world||busy)return;e.preventDefault();world.touring=false;world.zoom(e.deltaY);},{passive:false});
let layoutFrame=0;function scheduleLayout(){cancelAnimationFrame(layoutFrame);layoutFrame=requestAnimationFrame(()=>{world?.resize();if(world&&!busy&&!world.touring)world.focus(playing||document.body.classList.contains('previewing')?selected:-1);positionTargets();});}
function onFullscreenChange(){if(pointer&&canvas.hasPointerCapture(pointer.id))canvas.releasePointerCapture(pointer.id);pointer=null;syncFullscreen();scheduleLayout();}
document.addEventListener('fullscreenchange',onFullscreenChange);document.addEventListener('webkitfullscreenchange',onFullscreenChange);window.addEventListener('resize',scheduleLayout);window.visualViewport?.addEventListener('resize',scheduleLayout);document.addEventListener('visibilitychange',()=>last=0);
function animate(now){requestAnimationFrame(animate);if(document.hidden||failed){last=0;return;}const dt=last?Math.min(.08,(now-last)/1000):0;last=now;time+=dt;if(!busy&&cameraKeys.size){world?.pan((cameraKeys.has('ArrowRight')?1:0)-(cameraKeys.has('ArrowLeft')?1:0),(cameraKeys.has('ArrowUp')?1:0)-(cameraKeys.has('ArrowDown')?1:0),dt);}if(world)world.musicLevels=music.readLevels(dt);world?.updateWorld(time,dt,reduced);if(busy&&world?.sequence?.kind==='assembly'){$('stagePhase').textContent=({moving:t('平稳抵达','ARRIVING'),settled:t('镜头已就位','CAMERA SETTLED'),building:t('建筑正在搭建','BUILDING THE DOMAIN'),board:t('棋盘展开','REVEALING THE BOARD')})[canvas.dataset.arrival]||'';}positionTargets();}
function fallback(error){failed=true;world=null;$('loading').hidden=true;document.body.classList.add('map-fallback');phase('');openGame(campaign.current-2);notify(t('三维地图暂不可用，已切换为简洁棋盘。','3D unavailable. The accessible board is ready.'));console.error('Group sudoku map unavailable',error);}
canvas.addEventListener('webglcontextlost',e=>{e.preventDefault();fallback('WebGL context lost');});sync();
try{await document.fonts.ready;world=new SudokuAtlas(canvas);world.decorationSeconds=decorationSeconds;world.setMapStyle(mapStyle);REGIONS.forEach((r,i)=>world.paint(i,{values:campaign.board(r.n),selected:-1,cells:model.initial(r.n).map(v=>({classes:v?'given':''}))}));world.restore(campaign.completed);world.updateWorld(0,0,true);$('loading').classList.add('done');setTimeout(()=>$('loading').hidden=true,750);const preview=Number(new URLSearchParams(location.search).get('preview'));if(Number.isInteger(preview)&&preview>=2&&preview<=9)previewArchitecture(preview-2);else if(campaign.completed.length===8)showAtlas(true);else openGame(campaign.current-2);animate(performance.now());}catch(error){fallback(error);}
