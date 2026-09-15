import * as C from './cube-core.mjs';
import {CubeView} from './cube-view.mjs?v=20260915d';
import {LESSONS,lessonHTML} from './lessons.mjs?v=20260915d';
import {verifyCertificate} from './certificate.mjs';
const $=id=>document.getElementById(id);
const escapeHTML=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const colors={U:'#eee5cd',R:'#b96854',F:'#759d8b',D:'#d8b775',L:'#d09263',B:'#668da9'};
let currentLesson=0,turns=1,mode='algorithm',moves=[],snapshots=[],step=0,furthestStep=0,history=[],historyIndex=0,playing=false,busy=false,generation=0;
const view=new CubeView($('cube'),{onMove:manualMove,onInspect:hit=>message(`${hit.face} 面 · 当前贴纸 ${hit.label}。拖动色块可转动这一面。`)});
function message(text,error=false){$('status').textContent=text;$('status').classList.toggle('error',error);}
function renderMath(root){if(!window.katex)return;root.querySelectorAll('[data-tex]').forEach(el=>{try{window.katex.render(el.dataset.tex,el,{displayMode:el.dataset.display==='true',throwOnError:true,strict:'ignore'});}catch(e){el.textContent=el.dataset.tex;el.classList.add('math-error');console.error(e);}});}
function cycleText(p,names){const cs=C.cycles(p);return cs.length?cs.map(c=>'('+c.map(i=>names[i]).join(' → ')+')').join(' '):'e';}
function syncState(){
  const s=C.invariants(view.state),solved=C.equal(view.state,C.identity());
  $('stateBadge').textContent=s.legal?(solved?'已复原':'合法状态'):'不可达 · 拆装示例';$('stateBadge').classList.toggle('invalid',!s.legal);
  $('twistValue').textContent=s.twist;$('twistValue').classList.toggle('bad',!!s.twist);
  $('flipValue').textContent=s.flip;$('flipValue').classList.toggle('bad',!!s.flip);
  $('parityValue').textContent=`${s.cornerParity?'奇':'偶'} / ${s.edgeParity?'奇':'偶'}`;$('parityValue').classList.toggle('bad',s.cornerParity!==s.edgeParity);
  const fullCycles=C.cycles(C.mobilePermutation(view.state));
  $('cycleDisplay').innerHTML=`<p><b>角位置</b>${cycleText(C.inverse(s.cp),C.CORNERS)}</p><p><b>棱位置</b>${cycleText(C.inverse(s.ep),C.EDGES)}</p><p><b>完整贴纸</b>阶 ${C.order(view.state)} <span>· 轮换长度 ${fullCycles.length?fullCycles.map(c=>c.length).join(', '):'1'}</span>${s.legal?'':'（装配置换；不属于魔方群）'}</p>`;
  const at=C.inverse(view.state);
  $('cubeNet').innerHTML=C.FACES.map((f,k)=>`<div class="net-face" data-face="${f}" aria-label="${f} 面">${C.FACELETS.slice(k*9,k*9+9).map((_,j)=>{const source=C.FACELETS[at[k*9+j]];return `<span class="net-sticker" style="background:${colors[source.face]}" title="${f}${j+1} ← ${source.label}">${source.label}</span>`;}).join('')}</div>`).join('');
  $('orientationDisplay').innerHTML=`<div class="orientation-display"><p>角序：${C.CORNERS.join(' · ')}<br>朝向：${s.co.join(' , ')}</p><p>棱序：${C.EDGES.join(' · ')}<br>朝向：${s.eo.join(' , ')}</p><p>贴纸轮换：${escapeHTML(cycleText(view.state,C.FACELETS.map(f=>f.label)))}</p></div>`;
  $('cube').setAttribute('aria-label',`三阶魔方，${s.legal?(solved?'已复原':'合法状态'):'不可达装配状态'}。角扭转和 ${s.twist}，棱翻转和 ${s.flip}。可用下方面按钮操作，详细文字状态在状态与不变量中。`);
  syncControls();
}
function syncControls(){
  const algorithm=mode==='algorithm';
  $('stepCount').textContent=algorithm?`${step} / ${moves.length}`:`${historyIndex} 步`;
  $('timeline').max=algorithm?moves.length:0;$('timeline').value=algorithm?step:0;$('timeline').disabled=!algorithm||busy||!moves.length;
  $('previousStep').disabled=!algorithm||!step||busy;$('nextStep').disabled=!algorithm||step>=moves.length||busy;
  $('play').disabled=!algorithm||!moves.length;$('play').textContent=playing?'Ⅱ 暂停':'▶ 播放';
  $('undo').disabled=busy||(algorithm?!step:!historyIndex);$('redo').disabled=busy||(algorithm?step>=furthestStep:historyIndex>=history.length);
  $('sequence').querySelectorAll('button').forEach((b,i)=>{b.classList.toggle('done',i<step);b.classList.toggle('current',i===step-1);b.setAttribute('aria-current',i===step-1?'step':'false');b.disabled=busy;});
  $('faceButtons').querySelectorAll('button').forEach(b=>b.disabled=busy);
}
function abort(){playing=false;generation++;view.setState(view.state);busy=false;syncControls();}
function renderSequence(){$('sequence').innerHTML=mode==='algorithm'?moves.map((m,i)=>`<button data-step="${i+1}" title="跳到第 ${i+1} 步" aria-label="跳到第 ${i+1} 步 ${C.token(m)}">${C.token(m)}</button>`).join(''):'';}
function loadAlgorithm(text,{end=false,note}={}){
  let parsed;try{parsed=C.parseAlgorithm(text);}catch(e){message(e.message,true);return false;}
  abort();mode='algorithm';moves=parsed;snapshots=[C.identity()];for(const m of moves)snapshots.push(C.compose(snapshots.at(-1),C.movePermutation(m)));
  step=end?moves.length:0;furthestStep=step;history=[];historyIndex=0;$('algorithm').value=text;view.setState(snapshots[step]);renderSequence();syncState();message(note||`已载入 ${moves.length} 步，从复原态开始。按播放或逐步前进。`);return true;
}
function freeState(state=C.identity(),note='自由操作。拖动色块或使用面按钮。'){
  abort();mode='free';history=[];historyIndex=0;step=0;view.setState(state);renderSequence();syncState();message(note);
}
async function manualMove(move){
  if(busy)return;if(mode!=='free'){playing=false;mode='free';history=[];historyIndex=0;renderSequence();}
  const before=[...view.state],g=generation;busy=true;syncControls();const done=await view.turn(move);if(!done||g!==generation)return;
  history=history.slice(0,historyIndex);history.push({move,before,after:[...view.state]});historyIndex++;busy=false;syncState();message(`已转动 ${C.token(move)}。${C.invariants(view.state).legal?'':'转面保持不变量，仍无法消除拆装造成的障碍。'}`);
}
async function algorithmStep(direction){
  if(busy||mode!=='algorithm'||step+direction<0||step+direction>moves.length)return false;
  const g=generation,m=direction>0?moves[step]:C.invertMoves([moves[step-1]])[0];busy=true;syncControls();
  const done=await view.turn(m);if(!done||g!==generation)return false;step+=direction;furthestStep=Math.max(furthestStep,step);busy=false;syncState();message(`第 ${step} / ${moves.length} 步${step===moves.length?' · 演示完成':''}。`);return true;
}
async function togglePlay(){
  if(playing){playing=false;syncControls();message('已暂停；当前一步完成后停下。');return;}
  if(busy||mode!=='algorithm'||!moves.length)return;if(step===moves.length){step=0;view.setState(snapshots[0]);}
  playing=true;syncState();const g=generation;
  while(playing&&g===generation&&step<moves.length){const ok=await algorithmStep(1);if(!ok)break;}
  if(g===generation){playing=false;syncControls();}
}
function seek(n){abort();if(mode!=='algorithm')return;step=Math.max(0,Math.min(moves.length,n));furthestStep=Math.max(furthestStep,step);view.setState(snapshots[step]);syncState();message(`已定位到第 ${step} / ${moves.length} 步。`);}
async function undoRedo(direction){
  playing=false;if(mode==='algorithm'){if(direction>0&&step>=furthestStep)return;await algorithmStep(direction);return;}
  if(busy||historyIndex+direction<0||historyIndex+direction>history.length)return;
  const entry=history[direction>0?historyIndex:historyIndex-1],move=direction>0?entry.move:C.invertMoves([entry.move])[0],g=generation;busy=true;syncControls();
  const done=await view.turn(move);if(!done||g!==generation)return;historyIndex+=direction;busy=false;syncState();message(direction>0?'已重做一步。':'已撤销一步。');
}
function buildGeneratorTable(){const target=$('generatorTable');if(!target)return;target.innerHTML=`<table><thead><tr><th>面</th><th>角朝向向量</th><th>棱朝向向量</th></tr></thead><tbody>${C.FACES.map(f=>{const s=C.cubies(C.MOVES[f]);return `<tr><td>${f}</td><td class="data-vector">${s.co.join(' ')}</td><td class="data-vector">${s.eo.join(' ')}</td></tr>`;}).join('')}</tbody></table>`;}
function selectLesson(i,{scroll=false,hash=true}={}){
  if(i<0||i>=LESSONS.length)return;currentLesson=i;$('lesson').innerHTML=lessonHTML(i);$('chapters').querySelectorAll('button').forEach((b,j)=>{if(j===i)b.setAttribute('aria-current','step');else b.removeAttribute('aria-current');});
  buildGeneratorTable();renderMath($('lesson'));if(hash)window.history.replaceState(null,'',`#${LESSONS[i].id}`);
  if(scroll){$('lesson').scrollIntoView({behavior:preferences.reduced?'auto':'smooth',block:'start'});$('lesson').focus({preventScroll:true});}
}
async function runCertificate(){
  const button=$('verifyCertificate'),log=$('certificateLog');button.disabled=true;log.classList.remove('error');log.textContent='正在重建置换并检查轨道…';
  try{const response=await fetch('./certificate.json');if(!response.ok)throw Error(`证书下载失败：${response.status}`);const data=await response.json(),start=performance.now(),result=verifyCertificate(data);log.textContent=`验证通过 · ${result.nodes} 个操作词节点，18 层固定点检查。\n角轨道：${result.orbits.slice(0,7).map(o=>o.length).join(' × ')}。\n棱轨道：${result.orbits.slice(7).map(o=>o.length).join(' × ')}。\n下界 = 上界 = ${result.lowerBound.toLocaleString('en-US')}。\n本次复核耗时 ${Math.max(1,Math.round(performance.now()-start))} ms。`;log.style.whiteSpace='pre-line';}
  catch(e){log.textContent=`验证未完成：${e.message}`;log.classList.add('error');}finally{button.disabled=false;}
}
const saved=(()=>{try{return JSON.parse(localStorage.getItem('rubik-notebook.v1')||'{}');}catch{return {};}})();
const preferences={speed:[160,350,650].includes(saved.speed)?saved.speed:350,labels:!!saved.labels,highlight:!!saved.highlight,reduced:typeof saved.reduced==='boolean'?saved.reduced:matchMedia('(prefers-reduced-motion: reduce)').matches,textSize:saved.textSize==='large'?'large':'normal'};
function applyPreferences(){view.duration=preferences.reduced?0:preferences.speed;view.labels=preferences.labels;view.highlight=preferences.highlight;view.draw();document.documentElement.style.setProperty('--reading',preferences.textSize==='large'?'18px':'16px');$('speed').value=preferences.speed;$('labels').checked=preferences.labels;$('highlight').checked=preferences.highlight;$('reducedMotion').checked=preferences.reduced;$('textSize').value=preferences.textSize;try{localStorage.setItem('rubik-notebook.v1',JSON.stringify(preferences));}catch{}}
$('chapters').innerHTML=LESSONS.map((l,i)=>`<button data-lesson="${i}"><span>${String(i+1).padStart(2,'0')}</span>${l.short}</button>`).join('');
$('faceButtons').innerHTML=['R','U','F','D','L','B'].map(f=>`<button data-face="${f}" aria-label="转动 ${f} 面">${f}</button>`).join('');
$('faceButtons').addEventListener('click',e=>{const b=e.target.closest('[data-face]');if(b)manualMove({face:b.dataset.face,turns});});
document.querySelectorAll('[data-turns]').forEach(b=>b.addEventListener('click',()=>{turns=Number(b.dataset.turns);document.querySelectorAll('[data-turns]').forEach(x=>x.setAttribute('aria-pressed',String(x===b)));}));
$('homeView').addEventListener('click',()=>{view.home();message('已恢复观察角度；魔方状态保持。');});
$('reset').addEventListener('click',()=>freeState());$('scramble').addEventListener('click',()=>loadAlgorithm(C.scramble().map(C.token).join(' '),{end:true,note:'已做 20 步随机转动。此为随机操作词，并非均匀抽取所有合法状态；可逐步撤销。'}));
$('undo').addEventListener('click',()=>undoRedo(-1));$('redo').addEventListener('click',()=>undoRedo(1));
$('algorithmForm').addEventListener('submit',e=>{e.preventDefault();loadAlgorithm($('algorithm').value);});
$('play').addEventListener('click',togglePlay);$('previousStep').addEventListener('click',()=>{playing=false;algorithmStep(-1);});$('nextStep').addEventListener('click',()=>{playing=false;algorithmStep(1);});
$('timeline').addEventListener('input',e=>seek(Number(e.target.value)));
$('sequence').addEventListener('click',e=>{const b=e.target.closest('[data-step]');if(b)seek(Number(b.dataset.step));});
$('chapters').addEventListener('click',e=>{const b=e.target.closest('[data-lesson]');if(b)selectLesson(Number(b.dataset.lesson),{scroll:matchMedia('(max-width: 780px)').matches});});
$('lesson').addEventListener('click',e=>{
  const b=e.target.closest('[data-alg],[data-action],[data-next],[data-state-alg],#verifyCertificate');if(!b)return;
  if(b.id==='verifyCertificate'){runCertificate();return;}
  if(b.hasAttribute('data-next')){selectLesson(Number(b.dataset.next),{scroll:true});return;}
  if(b.hasAttribute('data-state-alg')){loadAlgorithm(b.dataset.stateAlg,{end:true,note:'已显示所选循环子群元素。'});return;}
  if(b.hasAttribute('data-alg')){loadAlgorithm(b.dataset.alg);return;}
  if(b.dataset.action==='free')freeState();else freeState(C.impossible(b.dataset.action),'已模拟一个不可达的拆装状态。观察红色不变量；合法转动保持这个障碍。');
});
$('lesson').addEventListener('keydown',e=>{if((e.key==='Enter'||e.key===' ')&&e.target.matches('[data-state-alg]')){e.preventDefault();e.target.dispatchEvent(new MouseEvent('click',{bubbles:true}));}});
$('settingsOpen').addEventListener('click',()=>{$('settings').showModal();});$('settingsClose').addEventListener('click',()=>$('settings').close());
$('settings').addEventListener('click',e=>{if(e.target===$('settings')){const r=$('settings').getBoundingClientRect();if(e.clientX<r.left||e.clientX>r.right||e.clientY<r.top||e.clientY>r.bottom)$('settings').close();}});
for(const [id,key] of [['speed','speed'],['labels','labels'],['highlight','highlight'],['reducedMotion','reduced'],['textSize','textSize']])$(id).addEventListener('change',e=>{preferences[key]=e.target.type==='checkbox'?e.target.checked:id==='speed'?Number(e.target.value):e.target.value;applyPreferences();});
document.addEventListener('keydown',e=>{
  if(e.ctrlKey||e.metaKey||e.altKey||e.repeat||$('settings').open||e.target.closest('input,textarea,select,button,a,summary,[role="button"]'))return;
  const f=e.key.toUpperCase();if(C.FACES.includes(f)){e.preventDefault();manualMove({face:f,turns:e.shiftKey?-1:turns});}
  else if(e.code==='Space'){e.preventDefault();togglePlay();}
});
window.addEventListener('hashchange',()=>{const i=LESSONS.findIndex(l=>`#${l.id}`===location.hash);if(i>=0)selectLesson(i,{hash:false});});
applyPreferences();selectLesson(Math.max(0,LESSONS.findIndex(l=>`#${l.id}`===location.hash)),{hash:false});loadAlgorithm("R R R R");
if(!window.katex)window.addEventListener('load',()=>renderMath($('lesson')),{once:true});
