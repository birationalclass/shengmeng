import {groups,validate,Closure} from './model.mjs';
import {Scene} from './scene.mjs?v=arena-a1';
const $=id=>document.getElementById(id);let en=false,g=groups.S3,seeds=new Set([1,2]),engine=null,playing=false,mode='continuous',targetRound=0,current=null,history=[],speed=1;
const tr=(zh,english)=>en?english:zh;
const scene=new Scene($('canvas'),toggleSeed);
function toggleSeed(id){if(engine)return;if(seeds.has(id))seeds.delete(id);else seeds.add(id);scene.selection(seeds);renderPalette();render();}
function renderPalette(){ $('palette').replaceChildren(...g.labels.map((label,id)=>{const b=document.createElement('button');b.setAttribute('aria-pressed',seeds.has(id));b.disabled=!!engine;b.innerHTML=`<b>${id+1}</b><small>${label}</small>`;b.setAttribute('aria-label',`${id+1}: ${label}`);b.onclick=()=>toggleSeed(id);return b;})); }
function render(){
  document.documentElement.lang=en?'en':'zh-CN';document.querySelectorAll('[data-zh]').forEach(el=>el.innerHTML=en?el.dataset.en:el.dataset.zh);$('lang').textContent=en?'中文':'EN';
  document.title=tr('生成元实验室 · 代数学','Generator laboratory · Algebra');$('fullscreen').setAttribute('aria-label',tr('全屏','Fullscreen'));document.querySelector('header a').setAttribute('aria-label',tr('返回代数学','Back to algebra'));$('canvas').setAttribute('aria-label',tr('群元素泡泡动画；点击泡泡或起点加号选择元素','Group element bubbles; select bubbles or use the seed picker'));
  $('seedTokens').replaceChildren(...[...seeds].map(id=>{const b=document.createElement('button');b.textContent=id+1;b.title=g.labels[id];b.disabled=!!engine;b.onclick=()=>toggleSeed(id);return b;}));$('setLabel').textContent=`${g.name} · ⟨${[...seeds].map(i=>g.labels[i]).join(', ')||'…'}⟩`;
  $('round').textContent=String(engine?.round||0).padStart(2,'0');$('roundLabel').textContent=tr('当前轮次','Current round');$('size').textContent=`${scene.present.size} / ${g.labels.length}`;
  $('hint').textContent=engine?'':tr('点击泡泡，选择起点','Tap bubbles to choose seeds');
  $('play').textContent=engine?.done?'✓':playing?'Ⅱ':'▶'; $('play').setAttribute('aria-label',engine?.done?tr('已闭合','Closed'):playing?tr('暂停','Pause'):tr('开始生成','Generate')); $('play').title=$('play').getAttribute('aria-label');
  $('play').disabled=!seeds.size||!!engine?.done;$('step').disabled=!seeds.size||playing||!!engine?.done;$('oneRound').disabled=$('step').disabled;
  document.querySelectorAll('[data-group]').forEach(b=>{b.disabled=!!engine;b.setAttribute('aria-pressed',groups[b.dataset.group]===g);});$('customOpen').disabled=!!engine;$('seedOpen').disabled=!!engine;$('opCount').textContent=engine?`${engine.count} ${tr('次','products')}`:'0';
  $('convention').textContent=g===groups.S3?tr('置换乘法从右向左作用。','Permutation composition acts right to left.'):g===groups.D4?tr('r 为旋转 90°，s 为反射；sr = r⁻¹s。','r rotates 90°, s reflects; sr = r⁻¹s.'):g===groups.Q8?'i² = j² = k² = ijk = −1':tr('e 为单位元。','e is the identity.');
  $('identity').textContent=`${tr('单位元','Identity')} · ${g.e+1} = ${g.labels[g.e]}`;
  $('progress').style.width=engine?`${engine.cursor/engine.pairs.length*100}%`:'0%';
  $('summary').textContent=engine?.done?tr(`已闭合：⟨S⟩ 有 ${engine.elements.size} 个元素${engine.elements.size===g.labels.length?'，生成整个群。':'，是一个真子群。'}最后一轮没有新增元素。`,`Closed: ⟨S⟩ has ${engine.elements.size} elements${engine.elements.size===g.labels.length?' and is the whole group.':', a proper subgroup.'} The final round added nothing.`):engine?tr(`第 ${engine.round} 轮 · 轮初 ${engine.snapshot.length} 个元素 · ${engine.cursor} / ${engine.pairs.length} 个有序乘积`,`Round ${engine.round} · ${engine.snapshot.length} starting elements · ${engine.cursor} / ${engine.pairs.length} ordered products`):tr('完整检查平方与两种碰撞方向，直到集合稳定。','Check squares and both collision directions until the set stabilizes.');
  document.querySelector('.size-ring').style.setProperty('--amount',`${scene.present.size/g.labels.length*360}deg`);
  document.querySelector('.pips').textContent=Array.from({length:Math.max(3,engine?.round||0)},(_,i)=>i===(engine?.round||1)-1?'●':'·').join(' ');
  $('outcome').textContent=engine?.done?tr(`已闭合 · ${engine.elements.size===g.labels.length?'生成整个群':'生成真子群'}`,`Closed · ${engine.elements.size===g.labels.length?'whole group':'proper subgroup'}`):'';
  for(const [id,zh,eng] of [['reset','重新选择','Reset'],['step','单次交互','One interaction'],['oneRound','运行一轮','One round'],['help','实验规则','How it works'],['recordOpen','生成轨迹','Discovery trail'],['seedOpen','选择起点','Choose seeds'],['customOpen','自定义群','Custom group']]){$(id).title=tr(zh,eng);$(id).setAttribute('aria-label',tr(zh,eng));}
  document.querySelectorAll('[data-speed]').forEach(b=>b.setAttribute('aria-pressed',Number(b.dataset.speed)===speed));
  renderOperation();renderHistory();
}
function renderOperation(){if(!current){$('equation').textContent='';$('stage').textContent='';return;}const o=current;
  $('equation').innerHTML=`${o.a===o.b?`${o.a+1}²`:`${o.a+1} · ${o.b+1}`} <span style="color:var(--gold)">= ${o.c+1}</span><small>${g.labels[o.a]} · ${g.labels[o.b]} = ${g.labels[o.c]}</small>`;
  $('stage').textContent=o.fresh?tr('✦ 新元素','✦ New element'):tr('已存在','Already present');
}
function renderHistory(){ $('history').replaceChildren(...history.map(o=>{const div=document.createElement('div');div.className='discovery';div.innerHTML=`<b>${o.a+1} · ${o.b+1} → ${o.c+1}</b><small>${tr('第','Round ')}${o.round}${tr(' 轮','')} · ${g.labels[o.c]}</small>`;return div;}));if(!history.length)$('history').innerHTML=`<p class="tiny">${tr('等待第一次生成…','Waiting for the first discovery…')}</p>`;}
function reset(){engine=null;playing=false;current=null;history=[];scene.enabled=true;scene.reset(g,seeds);renderPalette();render();}
function launch(kind){if(!seeds.size||engine?.done)return;if(!engine){engine=new Closure(g,seeds);scene.enabled=false;renderPalette();}mode=kind;targetRound=engine.cursor===engine.pairs.length?engine.round+1:engine.round;playing=true;if(!scene.active)next();render();}
function next(){current=engine.next();if(!current){playing=false;render();return;}scene.start(current);render();}
function completed(){if(current.fresh)history.push(current);if(mode==='step'||(mode==='round'&&engine.round===targetRound&&engine.cursor===engine.pairs.length))playing=false;
  // A full no-growth round proves closure, even in single-step mode.
  if(engine.cursor===engine.pairs.length&&!engine.added){engine.done=true;playing=false;}
  render();if(playing)next();}
$('play').onclick=()=>{if(playing){playing=false;render();}else launch('continuous');};$('step').onclick=()=>launch('step');$('oneRound').onclick=()=>launch('round');$('reset').onclick=reset;
$('lang').onclick=()=>{en=!en;render();};
document.querySelectorAll('[data-group]').forEach(b=>b.onclick=()=>{g=groups[b.dataset.group];seeds=new Set(g===groups.S3?[1,2]:g===groups.C6?[1]:g===groups.Q8?[2,4]:[1,4]);reset();});
document.querySelectorAll('[data-speed]').forEach(b=>b.onclick=()=>{speed=Number(b.dataset.speed);render();});
for(const [button,dialog] of [['help','rules'],['recordOpen','records'],['seedOpen','seeds'],['customOpen','custom']])$(button).onclick=()=>{playing=false;render();$(dialog).showModal();};
document.querySelectorAll('dialog .close').forEach(b=>b.onclick=()=>b.closest('dialog').close());
$('import').onclick=()=>{try{const table=$('tableInput').value.trim().split(/\n/).map(r=>r.trim().split(/[\s,]+/).map(x=>Number(x)-1)),e=validate(table);g={name:'G',table,e,labels:table.map((_,i)=>i===e?'e':`g${i+1}`)};seeds=new Set([table.length===1?0:e===0?1:0]);$('custom').close();reset();}catch(err){const messages={SIZE:['格式错误：请输入 1–16 阶方阵，每项为 1 到 n 的整数。','Enter a square table of order 1–16 with integer entries from 1 to n.'],IDENTITY:['没有双侧单位元。','No two-sided identity.'],INVERSE:['有元素没有双侧逆元。','An element has no two-sided inverse.'],ASSOCIATIVE:['此乘法不满足结合律，不能定义群。','This multiplication is not associative and does not define a group.']};$('error').textContent=(messages[err.message]||['输入无效','Invalid input'])[en?1:0];}};
$('fullscreen').onclick=async()=>{try{if(document.fullscreenElement)await document.exitFullscreen();else await document.documentElement.requestFullscreen();}catch{$('summary').textContent=tr('浏览器未允许全屏。','Fullscreen is unavailable.');}};document.addEventListener('fullscreenchange',()=>{$('fullscreen').textContent=document.fullscreenElement?'▫':'□';});
document.addEventListener('visibilitychange',()=>{if(document.hidden){playing=false;render();}});
// Prevent leftover focus from accidentally activating buttons with lesson keys.
for(const type of ['keydown','keyup'])document.addEventListener(type,e=>{if((e.key==='Enter'||e.key===' ')&&e.target.closest('button,a')&&!e.ctrlKey&&!e.metaKey&&!e.altKey)e.preventDefault();});
let previous=performance.now();function frame(now){const dt=Math.min((now-previous)/1000,.04);previous=now;const finished=scene.tick(playing?dt*speed:engine?0:dt,playing);scene.draw();if(finished)completed();requestAnimationFrame(frame);}reset();requestAnimationFrame(frame);
