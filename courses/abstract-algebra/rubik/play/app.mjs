import {createCube, compose, inverse, equal, power, analyze} from './cube-model.mjs?v=20261105a';
import {CubeView} from './cube-view.mjs?v=20261105a';
const $=id=>document.getElementById(id);
const palette={U:'#eee5cd',R:'#b96854',F:'#759d8b',D:'#d8b775',L:'#d09263',B:'#668da9'};
let model=createCube(3),moves=[],prefix=[],g=model.identity(),analysis=analyze(g),repeats=0n,step=0;
let playing=false,busy=false,dirty=false,manual=false,epoch=0;
const view=new CubeView($('cube'),model,{onMove:m=>record(m),onInspect:f=>message(`贴片位置 ${model.facelets[f.id]?.label||f.label||''}。开启“贴片编号”可区分同色贴片。`)});
view.duration=matchMedia('(prefers-reduced-motion: reduce)').matches?0:320;
$('speed').value=String(view.duration);
const format=n=>n.toString();
const superscript=s=>String(s).replace(/[-0-9]/g,c=>({'-':'⁻','0':'⁰','1':'¹','2':'²','3':'³','4':'⁴','5':'⁵','6':'⁶','7':'⁷','8':'⁸','9':'⁹'}[c]));
function message(text,error=false){$('status').textContent=text;$('status').classList.toggle('error',error);}
function cancel(){epoch++;playing=false;busy=false;view.setState(view.state);render();}
function compute(){
 g=model.algorithmPermutation(moves);analysis=analyze(g);prefix=[model.identity()];
 for(const move of moves)prefix.push(compose(prefix.at(-1),model.movePermutation(move)));
 dirty=false;$('algorithm').removeAttribute('aria-invalid');
 const order=format(analysis.order);$('order').textContent=order;$('order').classList.toggle('long',order.length>7);
 $('orderSentence').textContent=analysis.order===1n?'这套操作就是恒等元，一次执行后所有贴片均在原位。':`这套操作最少重复 ${order} 次，全部贴片回到原位。`;
 $('orderEquation').textContent=`g${superscript(order)} = e`;
 $('cycleChips').replaceChildren(...analysis.cycleCounts.map(({length,count})=>{const s=document.createElement('span');s.textContent=`${length} 轮换 × ${count}`;return s;}));
 $('lcm').textContent=analysis.lengths.length?`ord(g) = lcm(${analysis.lengths.join(', ')}) = ${order}`:'没有非平凡轮换：ord(e) = 1';
 $('fixedCount').textContent=`${analysis.degree} 张编号贴片中，${analysis.moved} 张移动，${analysis.fixed} 张保持原位。`;
 render();
}
function render(){
 const ord=analysis.order||1n,atIdentity=equal(view.state,model.identity());
 $('repeatCount').textContent=format(repeats);$('stepCount').textContent=`本套 ${step} / ${moves.length} 步`;
 $('positionLabel').textContent=step?`g${superscript(repeats)} · 前 ${step} 步`:`g${superscript(repeats)}${atIdentity?' = e':''}`;
 const rem=repeats%ord;$('cycleProgress').value=Number((repeats>0n&&rem===0n?ord:rem)*10000n/ord);
 $('stateBadge').textContent=busy?'转动中':atIdentity?'全部贴片原位':'尚未复原';$('stateBadge').classList.toggle('changed',!atIdentity);
 $('play').textContent=playing?'Ⅱ 暂停':'▶ 重复至复原';$('play').setAttribute('aria-label',playing?'暂停播放':'重复操作直到复原');
 const locked=dirty||busy||playing;
 for(const id of ['once','next','beforeIdentity','atIdentity'])$(id).disabled=locked||moves.length===0;
 $('play').disabled=dirty||(!playing&&busy)||moves.length===0;
 $('previous').disabled=locked||(repeats===0n&&step===0)||moves.length===0;
 $('invert').disabled=dirty||busy||playing||moves.length===0;
 document.querySelectorAll('[data-face]').forEach(b=>b.disabled=busy||playing);
 $('nextMove').textContent=moves.length?`下一步 ${model.token(moves[step])}`:'恒等操作';
 const start=moves.length<=70?0:Math.max(0,step-18),end=moves.length<=70?moves.length:Math.min(moves.length,start+38);
 const chips=[];if(start){const s=document.createElement('span');s.textContent='…';chips.push(s);}
 for(let i=start;i<end;i++){const s=document.createElement('span');s.textContent=model.token(moves[i]);s.className=i===step?'current':i<step?'done':'';if(i===step)s.setAttribute('aria-current','step');chips.push(s);}
 if(end<moves.length){const s=document.createElement('span');s.textContent='…';chips.push(s);}
 $('sequence').replaceChildren(...chips);
}
function load(input=$('algorithm').value){
 cancel();manual=false;
 try{moves=model.parse(input);$('algorithm').value=moves.map(model.token).join(' ');repeats=0n;step=0;view.setState(model.identity());compute();$('exponent').value='0';message(moves.length?`已载入 ${moves.length} 步。每执行一套，计数增加 1。`:'空序列是恒等操作，阶为 1。');return true;}
 catch(error){dirty=true;$('algorithm').setAttribute('aria-invalid','true');$('order').textContent='—';$('orderEquation').textContent='';$('cycleChips').replaceChildren();$('lcm').textContent='载入操作后显示轮换分解。';$('fixedCount').textContent='';$('orderSentence').textContent='请修正操作序列后重新计算。';message(error.message,true);render();return false;}
}
function stateAt(k,s=0){return compose(power(g,k),prefix[s]||model.identity());}
function jump(k){if(dirty)return;cancel();manual=false;repeats=BigInt(k);step=0;view.setState(stateAt(repeats));$('exponent').value=format(repeats);render();message(`已显示 g${superscript(repeats)}。${equal(view.state,model.identity())?'全部编号贴片回到原位。':'尚未全部回到原位。'}`);}
async function advanceOne(version){
 if(!moves.length||dirty||version!==epoch)return false;
 busy=true;render();const ok=await view.turn(moves[step]);
 if(version!==epoch)return false;busy=false;if(!ok){render();return false;}
 step++;if(step===moves.length){step=0;repeats++;}render();return true;
}
async function run(single=false){
 if(playing){cancel();message(`已暂停：完成 ${repeats} 套，本套 ${step} 步。`);return;}
 if(dirty||busy||!moves.length)return;
 if(!single&&step===0&&repeats>0n&&repeats%analysis.order===0n)jump(0n);
 manual=false;const version=++epoch,target=single?repeats+1n:(repeats/analysis.order+1n)*analysis.order;playing=true;render();
 message(single?'逐步执行这一套操作。':`正在重复操作，目标为第 ${target} 次；可随时暂停或直接跳转。`);
 while(version===epoch&&repeats<target){if(!await advanceOne(version))break;}
 if(version!==epoch)return;playing=false;render();
 message(equal(view.state,model.identity())?`第 ${repeats} 次：全部编号贴片回到原位。ord(g) = ${analysis.order}。`:`已完成 ${repeats} 套，尚未复原。`);
}
function currentSelection(){const value=Number($('layerValue').value);return $('layerMode').value==='wide'?{depth:1,width:value}:{depth:value,width:1};}
function layers(reset=false){
 const wide=$('layerMode').value==='wide',old=Number($('layerValue').value),min=wide?2:1;
 $('layerValue').replaceChildren(...Array.from({length:model.size-min+1},(_,i)=>{const o=document.createElement('option');o.value=i+min;o.textContent=wide?`${i+min} 层`:`${i+min}`;return o;}));
 $('layerValue').value=String(reset?min:Math.max(min,Math.min(model.size,old||min)));
 $('layerLabel').textContent=wide?'一起转':'第几层';refreshButtons();
}
function refreshButtons(){
 const selection=currentSelection(),turns=Number($('turns').value);view.moveSelection=selection;
 $('faceButtons').replaceChildren(...['U','R','F','D','L','B'].map(face=>{const b=document.createElement('button');b.type='button';b.dataset.face=face;b.textContent=model.token({face,...selection,turns});b.setAttribute('aria-label',`试转并记录 ${b.textContent}`);b.style.setProperty('--face-color',palette[face]);b.onclick=()=>record({face,...currentSelection(),turns:Number($('turns').value)});return b;}));
 $('layerHint').textContent=$('layerMode').value==='wide'?`从所选面起，外侧 ${selection.width} 层同时转动${selection.width===model.size?'（整个魔方）':''}。`:`从所选面向内数，第 ${selection.depth} 层单独转动。${model.size} 阶可选 1–${model.size} 层。`;
 render();
}
async function record(move){
 if(busy||playing)return;
 if(!manual||dirty){cancel();moves=[];repeats=0n;step=0;view.setState(model.identity());manual=true;}
 const version=epoch;moves.push(move);$('algorithm').value=moves.map(model.token).join(' ');compute();busy=true;render();
 const ok=await view.turn(move);if(version!==epoch)return;busy=false;
 if(ok){repeats=1n;step=0;render();message(`已记录 ${moves.length} 步，这套操作的阶为 ${analysis.order}。点击“重复至复原”继续观察。`);}
}
$('algorithmForm').addEventListener('submit',e=>{e.preventDefault();load();});
$('algorithm').addEventListener('input',()=>{cancel();dirty=true;manual=false;$('order').textContent='—';$('orderEquation').textContent='';$('cycleChips').replaceChildren();$('lcm').textContent='载入操作后显示轮换分解。';$('fixedCount').textContent='';$('orderSentence').textContent='操作序列已修改，点击“计算并载入”。';message('编辑中。载入后从原位开始。');render();});
$('cubeSize').addEventListener('change',()=>{cancel();model=createCube(Number($('cubeSize').value));view.setModel(model);moves=[];prefix=[model.identity()];g=model.identity();analysis=analyze(g);repeats=0n;step=0;layers(true);load();$('cube').setAttribute('aria-label',`可交互 ${model.size} 阶魔方。拖动观察或试转，也可用操作按钮。`);});
$('layerMode').addEventListener('change',()=>layers(true));$('layerValue').addEventListener('change',refreshButtons);$('turns').addEventListener('change',refreshButtons);
$('play').onclick=()=>run();$('once').onclick=()=>run(true);
$('next').onclick=async()=>{if(busy||playing||dirty)return;manual=false;const v=++epoch;await advanceOne(v);if(v===epoch)message(`完成 ${repeats} 套，本套 ${step} 步。`);};
$('previous').onclick=()=>{if(busy||playing||dirty||(!repeats&&!step))return;cancel();manual=false;if(step)step--;else{repeats--;step=moves.length-1;}view.setState(stateAt(repeats,step));render();message('已倒退一步。');};
$('reset').onclick=()=>{if(dirty){cancel();view.setState(model.identity());repeats=0n;step=0;render();message('画面已归零；请先计算并载入编辑中的操作。');}else jump(0n);};
$('invert').onclick=()=>load(model.inverseMoves(moves).map(model.token).join(' '));$('clear').onclick=()=>load('');
$('beforeIdentity').onclick=()=>jump(analysis.order-1n);$('atIdentity').onclick=()=>jump(analysis.order);
$('jumpForm').addEventListener('submit',e=>{e.preventDefault();const input=$('exponent').value.trim();if(!/^\d{1,80}$/.test(input)){message('重复次数 k 须为非负整数（至多 80 位）。',true);return;}jump(BigInt(input));});
$('speed').onchange=()=>{view.duration=Number($('speed').value);};$('labels').onchange=()=>{view.labels=$('labels').checked;view.draw();};$('homeView').onclick=()=>view.home();
for(const b of document.querySelectorAll('[data-example]'))b.onclick=()=>load(b.dataset.example);
$('fullscreen').onclick=async()=>{try{if(document.fullscreenElement)await document.exitFullscreen();else if(document.documentElement.requestFullscreen)await document.documentElement.requestFullscreen();else message('此浏览器不提供原生全屏；当前页面可继续操作。');}catch{message('未能进入原生全屏，当前页面可继续操作。');}};
document.addEventListener('fullscreenchange',()=>{$('fullscreen').querySelector('span').textContent=document.fullscreenElement?'退出全屏':'全屏';view.draw();});
document.addEventListener('keydown',e=>{if(e.repeat||e.ctrlKey||e.metaKey||e.altKey||e.target.closest('input,textarea,select,[contenteditable]'))return;
 const face=e.key.toUpperCase();if('URFDLB'.includes(face)&&face.length===1){e.preventDefault();record({face,...currentSelection(),turns:e.shiftKey?-1:Number($('turns').value)});}else if(e.code==='Space'&&!e.target.closest('button,summary,a')){e.preventDefault();run();}
});
layers(true);load();
// Read-only diagnostics for mathematical and interaction regression checks.
window.cubeOrderLab={getState:()=>({size:model.size,moves:moves.map(m=>({...m})),permutation:[...g],state:[...view.state],order:format(analysis.order),repeats:format(repeats),step,playing,busy,dirty,manual,camera:{yaw:view.yaw,pitch:view.pitch}})};
