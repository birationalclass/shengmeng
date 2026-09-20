import {Campaign} from './campaign.mjs?v=world2';
import {SudokuAtlas,REGIONS} from './atlas.mjs?v=world2';
const $=id=>document.getElementById(id),model=window.AssociativitySudokuModel;
let storage;try{storage=localStorage;}catch{}
const campaign=new Campaign(model,storage);let selected=0,world,game,frame=0,last=0,time=0,reduced=matchMedia('(prefers-reduced-motion: reduce)').matches,toastTimer,failed=false,playing=false,boardState,mapStyle='parchment';
try{mapStyle=storage?.getItem('group-sudoku-map-style')||'parchment';}catch{}
const en=()=>window.CourseLanguage.language==='en',t=(zh,eng)=>en()?eng:zh;
function notify(message){$('toast').textContent=message;$('toast').hidden=false;clearTimeout(toastTimer);toastTimer=setTimeout(()=>$('toast').hidden=true,6500);}
function sync(){
 const done=campaign.completed,info=REGIONS[selected];$('progress').innerHTML=`${done.length} <span>/ 8</span>`;
 $('skillStatus').textContent=campaign.identityUnlocked?t('单位元卡 · 已解锁','Identity card · Unlocked'):t('单位元卡 · 待解锁','Identity card · Locked');
 $('unlockNote').textContent=campaign.identityUnlocked?t('在棋局中把单位元数字标红','Mark identity numbers in red'):t('通关 3×3 玉阶庭院获得','Complete the 3×3 Jade Court');
 $('progressDots').innerHTML=REGIONS.map(r=>`<i class="${done.includes(r.n)?'complete':''}"></i>`).join('');
 $('regionTitle').textContent=en()?info.en:info.zh;$('regionKicker').textContent=`DOMAIN ${String(selected+1).padStart(2,'0')} · ${info.group}`;
 $('regionSubtitle').textContent=`${info.n} × ${info.n} · ${done.includes(info.n)?t('已通关，可重访','Completed · Revisit'):t('以结合律补全乘法表','Complete a table through associativity')}`;
 $('enterText').textContent=done.includes(info.n)?t('重访棋局','Revisit board'):t('进入棋局','Enter the board');
 $('regionNav').innerHTML=REGIONS.map((r,i)=>`<button data-region="${i}" class="${done.includes(r.n)?'complete':''}" aria-current="${selected===i}">${r.n}×${r.n}<span>${en()?r.group:r.zh}</span></button>`).join('');
 $('pins').innerHTML=REGIONS.map((r,i)=>`<button class="map-pin ${done.includes(r.n)?'complete':''}" data-region="${i}" aria-current="${selected===i}" aria-label="${en()?r.en:r.zh} ${r.n}×${r.n}">${r.n}×${r.n}</button>`).join('');
 document.querySelector('.map-heading h1').innerHTML=t('群数独<span>八域之书</span>','Group Sudoku<span>BOOK OF EIGHT</span>');$('overview').textContent=t('全图','Atlas');$('language').textContent=en()?'中文':'EN';$('language').setAttribute('aria-label',t('切换到英文','Switch to Chinese'));$('motion').textContent=t('减少动态','Reduce motion');$('motion').setAttribute('aria-pressed',String(reduced));$('mapLead').textContent=t('穿过机械城邦，以法则补全世界。','Across clockwork cities, restore the laws of composition.');$('viewHint').textContent=playing?t('点击格子 · 数字键落子 · 拖动空地调整视角','Select a cell · Type a number · Drag the ground to orbit'):t('拖动观察 · 滚轮缩放 · 点击城邦启程','Drag to orbit · Scroll to zoom · Select a domain');$('closeGame').textContent=t('返回全图 ↗','Return to atlas ↗');$('settingsToggle').textContent=t('设置','Settings');world?.setProgress(done);positionPins();
}
function positionPins(){if(!world)return;for(const pin of $('pins').children){const p=world.project(+pin.dataset.region);pin.style.left=p.x*100+'%';pin.style.top=p.y*100+'%';pin.style.visibility=p.visible?'visible':'hidden';}}
function choose(i){selected=i;sync();openGame();}
function renderBoard(state){
 const restoreFocus=document.activeElement?.hasAttribute('data-board-cell');boardState=state;world?.paint(selected,state);
 const hits=$('boardHits');hits.innerHTML=state.cells.map((cell,k)=>`<button data-board-cell="${k}" aria-label="${cell.label}" aria-pressed="${state.selected===k}" tabindex="${state.selected===k?0:-1}"></button>`).join('');positionCells();if(restoreFocus)hits.querySelector(`[data-board-cell="${state.selected}"]`)?.focus({preventScroll:true});
}
function positionCells(){if(!world||!playing)return;const rect=canvas.getBoundingClientRect();for(const b of $('boardHits').children){const k=+b.dataset.boardCell,p=world.cellProjection(selected,k),q=world.cellProjection(selected,k%boardState.n===boardState.n-1?k-1:k+1),w=Math.max(15,Math.abs(p.x-q.x)*rect.width*.78);b.style.left=p.x*rect.width+'px';b.style.top=p.y*rect.height+'px';b.style.width=w+'px';b.style.height=w*.72+'px';b.style.visibility=p.visible?'visible':'hidden';}}
function openGame(){
 playing=true;sync();document.body.classList.add('playing');$('gamePanel').hidden=false;
 const region=REGIONS[selected];$('gameEyebrow').textContent=region.en;$('gameTitle').textContent=`${en()?region.en:region.zh} · ${region.n} × ${region.n}`;
 game?.destroy();game=window.AssociativitySudoku.render($('gameMount'),{level:region.n,values:campaign.board(region.n),completed:campaign.completed,fixedLevel:true,sceneBoard:true,requireIdentityUnlock:true,onRender:renderBoard,onChange:(n,v)=>{campaign.save(n,v);sync();},onComplete:(n,v)=>{campaign.save(n,v);sync();notify(n===3?t('玉阶庭院已点亮 · 获得单位元技能卡','Jade Court illuminated · Identity card unlocked'):t(`${n}×${n} 区域已点亮`,`${n}×${n} domain completed`));}});
 world?.resize();world?.focus(selected);$('gamePanel').scrollTop=0;
}
function closeGame(){playing=false;sync();document.body.classList.remove('playing');$('gamePanel').hidden=true;$('boardHits').innerHTML='';game?.destroy();game=null;world?.resize();world?.focus(-1);}
$('enterRegion').onclick=openGame;$('closeGame').onclick=closeGame;
$('boardHits').addEventListener('click',e=>{const b=e.target.closest('[data-board-cell]');if(b){game?.select(+b.dataset.boardCell);$('boardHits').querySelector(`[data-board-cell="${b.dataset.boardCell}"]`)?.focus({preventScroll:true});}});
$('boardHits').addEventListener('keydown',e=>{if(!game)return;const n=boardState.n,offset={ArrowLeft:-1,ArrowRight:1,ArrowUp:-n,ArrowDown:n}[e.key];if(offset){e.preventDefault();game.select((boardState.selected+offset+n*n)%(n*n));$('boardHits').querySelector(`[data-board-cell="${boardState.selected}"]`)?.focus({preventScroll:true});}else if(/^[1-9]$/.test(e.key)&&+e.key<=n){e.preventDefault();game.enter(+e.key);}else if(['Delete','Backspace'].includes(e.key)){e.preventDefault();game.enter(0);}});
$('settingsToggle').onclick=()=>{const panel=$('settingsPanel');panel.hidden=!panel.hidden;$('settingsToggle').setAttribute('aria-expanded',String(!panel.hidden));};
for(const input of document.querySelectorAll('[name="mapStyle"]')){input.checked=input.value===mapStyle;input.addEventListener('change',()=>{mapStyle=input.value;world?.setMapStyle(mapStyle);try{storage?.setItem('group-sudoku-map-style',mapStyle);}catch{}});}
for(const id of ['regionNav','pins'])$(id).addEventListener('click',e=>{const b=e.target.closest('[data-region]');if(b)choose(+b.dataset.region);});
$('overview').onclick=closeGame;$('language').onclick=()=>{window.CourseLanguage.language=en()?'zh':'en';document.documentElement.lang=en()?'en':'zh-CN';window.dispatchEvent(new Event('course-language'));sync();if(playing){$('gameTitle').textContent=`${en()?REGIONS[selected].en:REGIONS[selected].zh} · ${selected+2} × ${selected+2}`;}};
$('motion').onclick=()=>{reduced=!reduced;sync();};$('fullscreen').onclick=async()=>{try{if(document.fullscreenElement)await document.exitFullscreen();else await document.documentElement.requestFullscreen();}catch{notify(t('当前窗口不支持全屏','Fullscreen is not available'));}};
let pointer=null;const canvas=$('world');canvas.addEventListener('pointerdown',e=>{if(e.button!==0||!world)return;pointer={id:e.pointerId,x:e.clientX,y:e.clientY,startX:e.clientX,startY:e.clientY,moved:false};canvas.setPointerCapture(e.pointerId);});canvas.addEventListener('pointermove',e=>{if(!pointer||!world)return;const dx=e.clientX-pointer.x,dy=e.clientY-pointer.y;if(Math.hypot(e.clientX-pointer.startX,e.clientY-pointer.startY)>4)pointer.moved=true;if(pointer.moved)world.orbit(dx,dy);pointer.x=e.clientX;pointer.y=e.clientY;});canvas.addEventListener('pointerup',e=>{if(pointer&&!pointer.moved&&world){const r=canvas.getBoundingClientRect(),hit=world.pick((e.clientX-r.left)/r.width*2-1,1-(e.clientY-r.top)/r.height*2);if(hit>=0)choose(hit);}pointer=null;});canvas.addEventListener('pointercancel',()=>pointer=null);canvas.addEventListener('wheel',e=>{if(!world)return;e.preventDefault();world.zoom(e.deltaY);},{passive:false});
window.addEventListener('resize',()=>{world?.resize();if(world)world.focus(playing?selected:-1);positionPins();positionCells();});document.addEventListener('visibilitychange',()=>{last=0;});
function animate(now){frame=requestAnimationFrame(animate);if(document.hidden||failed){last=0;return;}const dt=last?Math.min(.08,(now-last)/1000):0;last=now;time+=dt;world?.updateWorld(time,dt,reduced);positionPins();positionCells();}
function fallback(error){failed=true;world=null;$('mapFallback').hidden=false;$('loading').hidden=true;document.body.classList.add('map-fallback');console.error('Group sudoku map unavailable',error);}
canvas.addEventListener('webglcontextlost',e=>{e.preventDefault();fallback('WebGL context lost');});
sync();
try{await document.fonts.ready;await new Promise(resolve=>requestAnimationFrame(resolve));world=new SudokuAtlas(canvas);world.setMapStyle(mapStyle);REGIONS.forEach((r,i)=>world.paint(i,{values:campaign.board(r.n),selected:-1,cells:campaign.board(r.n).map((v,k)=>({classes:model.initial(r.n)[k]?'given':''}))}));world.focus(-1);world.setProgress(campaign.completed);world.updateWorld(0,2,true);positionPins();$('loadStatus').textContent=t('八域已就绪','Eight domains are ready');$('loading').classList.add('done');setTimeout(()=>$('loading').hidden=true,750);animate(performance.now());}catch(error){fallback(error);}
