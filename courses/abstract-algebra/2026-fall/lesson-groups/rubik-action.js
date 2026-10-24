/* A labeled cube, not a canned animation: every endpoint is an exact permutation. */
(()=>{
 'use strict';
 const M=window.RubikActionModel;
 const S={recipe:"R U R' U'",base:M.identity(),round:0,phase:null,running:false,mode:'one',stage:0,proof:0,slots:54,numbers:true,scrambled:false,yaw:-.62,pitch:.46,selected:8};
 const en=()=>window.CourseLanguage?.language==='en',t=(zh,eng)=>en()?eng:zh;
 const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
 const math=tex=>window.katex.renderToString(tex,{displayMode:true,throwOnError:true,strict:'ignore'});
 let inspect=()=>({});
 function mount(root){
  let alive=true,raf=0,last=performance.now(),drag=null,hit=[];
  let p=M.word(S.recipe),cycles=M.cycles(p),N=M.order(p);
  function selectedCycle(){return cycles.find(c=>c.includes(S.selected));}
  function endpoint(){return S.phase?S.phase.before:M.at(S.base,p,S.round);}
  root.innerHTML=`<section class="rubik-lab" aria-label="${t('魔方与有限群作用','The cube and finite actions')}">
   <header class="rubik-heading"><h3>${t('同一套动作，为什么一定会回来？','Why must a fixed sequence return?')}</h3><p>${t('先分清位置、状态与操作，再亲手重复。','Distinguish positions, states and operations, then repeat a sequence.')}</p></header>
   <nav class="rubik-stages" aria-label="${t('讲解步骤','Teaching stages')}">${[['建模','Model'],['有限','Finite'],['重复','Repeat'],['证明','Proof']].map((pair,i)=>`<button type="button" data-rubik-stage="${i}"><b>0${i+1}</b><span>${t(...pair)}</span></button>`).join('')}</nav>
   <div class="rubik-view"><canvas width="900" height="620" tabindex="0" aria-label="${t('可拖动观察的三维魔方；数字是贴纸编号','Drag to rotate the cube; numbers identify stickers')}"></canvas><span class="rubik-start-label"></span><span class="rubik-move-label"></span><p class="rubik-drag-hint">${t('拖动观察 · 点击贴纸追踪','Drag to look around · Click a sticker to track it')}</p></div>
   <div class="rubik-live" aria-live="polite"><span data-round></span><span data-return></span><strong data-verdict></strong></div>
   <div class="rubik-recipes" role="group" aria-label="${t('选择固定操作串','Choose a fixed sequence')}">${M.presets.slice(0,3).map(w=>`<button type="button" data-rubik-word="${esc(w)}">${esc(w)}</button>`).join('')}</div>
   <form class="rubik-word-form"><label>${t('一轮动作（从左到右执行）','One round (execute left to right)')}<input aria-label="${t('自定义动作串','Custom move sequence')}" value="${esc(S.recipe)}" maxlength="120" spellcheck="false" autocomplete="off"></label><button type="submit">${t('使用','Use')}</button></form><p class="rubik-input-error" role="status" hidden></p>
   <div class="rubik-controls"><button type="button" data-once>${t('执行一轮','One round')}</button><button type="button" data-play></button><button type="button" data-reset>${t('回到起点','Reset to start')}</button><button type="button" data-start></button><button type="button" data-labels aria-pressed="${S.numbers}">${t('贴纸编号','Sticker labels')}</button></div>
   <div class="rubik-teaching"></div>
   <details class="rubik-source"><summary>${t('记号与参考','Notation and reference')}</summary><p>${t('这里只记录整面转动结束后的状态；转动动画中的中间姿态不是新的离散状态。动作串按屏幕从左到右执行；抽象群乘积 gh 仍按先 h 后 g 复合。','Only completed face turns count as discrete states. Intermediate animation poses do not. Move sequences run left to right; the abstract product gh still means h followed by g.')}</p><p><a href="https://www.bilibili.com/video/BV1Fyn26HEcY/" target="_blank" rel="noopener">${t('提问所附魔方参考视频 ↗','Cube video supplied with the question ↗')}</a></p></details>
  </section>`;
  const lab=root.querySelector('.rubik-lab'),canvas=lab.querySelector('canvas'),ctx=canvas.getContext('2d'),teaching=lab.querySelector('.rubik-teaching');
  if(!ctx){lab.textContent=t('当前浏览器无法绘制魔方，请更换支持 Canvas 的浏览器。','Canvas is unavailable in this browser.');window.CourseHealth?.report('D-RUBIK','魔方绘图不可用。','Cube rendering is unavailable.',{key:'rubik'});return()=>{};}
  const on=(selector,event,fn)=>lab.querySelector(selector).addEventListener(event,fn);
  function stop(){S.running=false;S.phase=null;}
  function recalc(){p=M.word(S.recipe);cycles=M.cycles(p);N=M.order(p);S.selected=(cycles.find(c=>c.length>1)||cycles[0])[0];}
  function setRecipe(word){const tokens=M.parse(word);if(!tokens.length)throw Error('empty');stop();S.recipe=tokens.join(' ');S.round=0;recalc();lab.querySelector('input').value=S.recipe;showTeaching();update();}
  function seek(n){stop();S.round=Math.max(0,Math.min(N,Number(n)));update();}
  function startRound(mode){if(S.round===N&&!S.phase)S.round=0;S.mode=mode;S.running=true;if(!S.phase)S.phase={tokens:M.parse(S.recipe),index:0,elapsed:0,before:M.at(S.base,p,S.round)};last=performance.now();update();}
  function showTeaching(){
   lab.dataset.stage=String(S.stage);
   lab.querySelectorAll('[data-rubik-stage]').forEach(b=>b.setAttribute('aria-current',Number(b.dataset.rubikStage)===S.stage?'step':'false'));
   if(S.stage===0){
    const net=which=>`<figure data-model-state="${which}"><figcaption>${math(which?'g\u00b7 x_0':'x_0')}</figcaption><div class="rubik-state-net">${M.faces.map((face,i)=>`<div aria-label="${face[0]}">${Array.from({length:9},(_,j)=>`<span data-net-slot="${i*9+j}"></span>`).join('')}</div>`).join('')}</div></figure>`;
    teaching.innerHTML=`<h4>${t('整个配色记录，才是 X 中的一个点','One whole coloring is one point of X')}</h4><p>${t('左、右各是一只完整魔方的六面记录。固定操作 g 把左边整个状态送到右边整个状态。','Each record contains all six faces of one cube. The fixed operation g sends the whole state on the left to the whole state on the right.')}</p><div class="rubik-state-pair">${net(0)}<span aria-hidden="true">g<br>→</span>${net(1)}</div><div class="rubik-model-pair"><article><h4>${t('位置集 P：54 个位置','Position set P: 54 slots')}</h4><p>${t('6 个面，每面 3×3 个位置。一个合法转动把这些位置重新排列；选一张编号贴纸看它去了哪里。','Six faces with 3×3 slots each. A legal turn permutes these slots. Track a labeled sticker to see the permutation.')}</p>${math(String.raw`G=\langle R,L,U,D,F,B\rangle\leq\operatorname{Sym}(P)`)}<p>${t('G 的元素是操作的效果；产生相同位置置换的动作串代表同一个元素。','An element of G is an operation effect. Sequences inducing the same slot permutation represent the same element.')}</p></article><article><h4>${t('状态集 X：整个魔方的状态','State set X: whole-cube states')}</h4><p>${t('一个点 x 现在表示整个魔方的配色。X 取从复原态出发、通过合法操作可达的所有状态。','A point x now represents a coloring of the entire cube. X is the set of all states reachable from the solved cube by legal operations.')}</p>${math(String.raw`g\cdot x=\text{${en()?'apply g to state x':'对状态 x 执行 g'}}`)}<p>${t('两种作用要分开：一张贴纸的位置，不等于整个魔方的状态。','Keep the actions distinct: one sticker position is not a whole-cube state.')}</p></article></div><div class="rubik-law">${math(String.raw`e\cdot x=x,\qquad(gh)\cdot x=g\cdot(h\cdot x)`)}<p>${t('不转就是单位元；两套操作接着做就是复合；倒序并反向转动给出逆操作。因此每个 g 在 X 上都是双射。','Doing nothing is the identity; executing operations successively is composition; reversing the sequence and every turn gives the inverse. Thus every g acts bijectively on X.')}</p></div>`;
   }else if(S.stage===1){
    teaching.innerHTML=`<h4>${t('不必数出精确总数，也能证明有限','Finiteness needs no exact cube-state count')}</h4><p>${t('固定魔方的整体朝向，只记录 54 个位置的颜色。每个位置至多 6 种选择。','Fix the whole cube orientation and record the colors at 54 slots. Each slot has at most six choices.')}</p><label class="rubik-range-label">${t('逐个记录位置','Record the slots one by one')}<input type="range" data-slot-range min="1" max="54" value="${S.slots}" aria-label="${t('记录的位置数','Number of recorded slots')}"></label><div class="rubik-slots" aria-hidden="true">${M.slots.map((s,i)=>`<span style="--tile:${s.color}" data-slot-cell="${i}"></span>`).join('')}</div><div data-finite-equation></div><p>${t('所有着色组成一个更大的有限集合 Ω。合法状态只是其中一部分：六种颜色各有九张、角块和棱块必须满足机械约束，都会继续减少状态数。','All colorings form a larger finite set Ω. Legal states are only a subset: nine stickers of each color and mechanical corner/edge constraints reduce the possibilities further.')}</p>${math(String.raw`X\subseteq\Omega=\{1,\ldots,6\}^{P},\qquad |X|\leq6^{54}<\infty`)}<p class="rubik-emphasis">${t('动画可以连续转动，数学模型中的状态仍是有限的离散集合。','The animation moves continuously, while the modeled endpoints form a finite discrete set.')}</p>`;
    on('[data-slot-range]','input',e=>{S.slots=Number(e.target.value);updateFinite();});updateFinite();
   }else if(S.stage===2){
    const lengths=cycles.filter(c=>c.length>1).map(c=>c.length);
    teaching.innerHTML=`<h4>${t('固定 g，完整的一套动作算一轮','Fix g: one full sequence is one round')}</h4><div class="rubik-return-formula">${math(String.raw`x_0\;\xrightarrow{g}\;g x_0\;\xrightarrow{g}\;g^2 x_0\;\xrightarrow{g}\;\cdots\;\xrightarrow{g}\;x_0`)}</div><label class="rubik-range-label">${t('查看某一轮结束时的状态','Inspect a completed round')}<input type="range" data-round-range min="0" max="${N}" value="${S.round}" aria-label="${t('已执行轮数','Completed rounds')}"></label><div class="rubik-near-return"><button type="button" data-before-return>${t('跳到回归前一轮','Go to the round before return')}</button><button type="button" data-final-round>${t('执行最后一轮','Perform the final round')}</button></div><h4>${t('追踪一个位置的循环','Track the cycle of one slot')}</h4><div class="rubik-cycle-picks">${cycles.filter(c=>c.length>1).map((c,i)=>`<button type="button" data-cycle-start="${c[0]}" aria-pressed="${c.includes(S.selected)}">${t('循环','Cycle')} ${i+1} · ${c.length}</button>`).join('')||`<span>${t('每个位置都固定','Every slot is fixed')}</span>`}</div><div class="rubik-cycle-track" data-cycle-track></div><p data-track-description></p><h4>${t('整只魔方一起回来','All slots return together')}</h4><div data-cycle-order>${math(String.raw`N=\operatorname{lcm}(${lengths.length?lengths.join(','):'1'})=${N}`)}</div><p>${t('只看一张贴纸回来了还不够；所有位置的循环都走完整数圈，整套操作才恢复恒等置换。上式省略了长度为 1 的固定位置。','One sticker returning is not enough. Every slot cycle must complete a whole number of laps to recover the identity permutation. Fixed slots of length one are omitted above.')}</p><p class="rubik-small">${t('N 对所有起点都有效。一个特定的彩色状态可能更早回来；贴纸编号帮助分辨同色贴纸，避免误把“颜色看似相同”当作置换已恢复。','N works for every start. A particular coloring may return sooner; labels distinguish same-colored stickers so that matching colors are not mistaken for the identity permutation.')}</p>`;
    on('[data-round-range]','input',e=>seek(e.target.value));on('[data-before-return]','click',()=>seek(N-1));on('[data-final-round]','click',()=>{seek(N-1);startRound('one');});
    teaching.querySelectorAll('[data-cycle-start]').forEach(b=>b.onclick=()=>{S.selected=Number(b.dataset.cycleStart);update();});updateCycle();
   }else{
    const proof=[
     [t('先用有限性找到重复','Finiteness gives a repetition'),String.raw`x_0,gx_0,\ldots,g^{m}x_0,\qquad m=|X|`,t('m+1 个状态落在 m 个可能状态里，必有 0≤i<j≤m，使 gⁱx₀=gʲx₀。','Among m+1 terms in a set of m states, two coincide: gⁱx₀=gʲx₀ for some 0≤i<j≤m.')],
     [t('再用逆操作退回起点','Use the inverse to return to the start'),String.raw`g^{-i}(g^i x_0)=g^{-i}(g^j x_0)\quad\Longrightarrow\quad x_0=g^{j-i}x_0`,t('两边同时作用 g⁻ⁱ，得到正数 d=j−i。重复 d 轮，回到原来选定的 x₀。','Apply g⁻ⁱ to both sides. The positive integer d=j−i is a return time to the chosen x₀.')],
     [t('循环可以一圈一圈继续','The same cycle repeats'),String.raw`g^d x_0=x_0\quad\Longrightarrow\quad g^{n+d}x_0=g^n x_0`,t('这里不需要 G 本身有限；只需 X 有限，且 g 的作用可逆。魔方的位置置换给出了可直接计算的共同回归次数 N。','G itself need not be finite. X must be finite and the action of g invertible. The cube slot permutation provides a computable common return time N.')]
    ];
    teaching.innerHTML=`<h4>${t('有限 + 可逆，缺一不可','Finite and invertible: both matter')}</h4><p>${t('有限性只能保证“某处重复”。逆操作才保证那个循环包含最初的状态。','Finiteness alone guarantees a repetition somewhere. Invertibility ensures the cycle contains the initial state.')}</p><div class="rubik-proof-steps">${proof.slice(0,S.proof+1).map((a,i)=>`<article><b>${i+1}. ${a[0]}</b>${math(a[1])}<p>${esc(a[2])}</p></article>`).join('')}</div><button type="button" data-proof-next ${S.proof===2?'disabled':''}>${S.proof===2?t('证明完成','Proof complete'):t('继续推理 →','Continue the argument →')}</button><details class="rubik-caveat"><summary>${t('为什么“集合有限”还不够？','Why is a finite set alone insufficient?')}</summary><p>${t('在 {0,1} 上令 T(0)=T(1)=0。从 1 出发得到 1→0→0→⋯，永不回到 1。因为 T 不可逆。这不是群作用。','On {0,1}, let T(0)=T(1)=0. Starting at 1 gives 1→0→0→⋯ and never returns to 1. T is not invertible, so this is not a group action.')}</p></details><p class="rubik-emphasis">${t('重复的是同一个固定操作 g。若每次随意换操作，上面的幂序列与证明就不再适用。','The same fixed operation g is repeated. Arbitrarily changing the operation at every step is not this power sequence.')}</p>`;
    on('[data-proof-next]','click',()=>{S.proof=Math.min(2,S.proof+1);showTeaching();});
   }
   requestAnimationFrame(()=>{window.dispatchEvent(new Event('lesson-math-changed'));window.LessonScreen?.refresh();});
  }
  function updateFinite(){const area=teaching.querySelector('[data-finite-equation]');if(!area)return;area.innerHTML=math(String.raw`${S.slots}\ \text{${en()?'slots':'个位置'}}:\quad 6^{${S.slots}}\ \text{${en()?'possible records at most':'种记录上界'}}`);teaching.querySelectorAll('[data-slot-cell]').forEach(c=>c.classList.toggle('is-recorded',Number(c.dataset.slotCell)<S.slots));window.dispatchEvent(new Event('lesson-math-changed'));}
  function updateCycle(){const track=teaching.querySelector('[data-cycle-track]');if(!track)return;const c=selectedCycle(),pos=M.power(p,S.round)[S.selected];track.innerHTML=c.map((j,i)=>`<span class="${j===pos?'is-current':''}" title="${t('位置','Slot')} ${j+1}">${j+1}<i>→</i></span>`).join('')+`<span class="rubik-cycle-loop">↺</span>`;teaching.querySelector('[data-track-description]').textContent=t(`这条循环有 ${c.length} 个位置；已走 ${S.round} 步，目前在位置 ${pos+1}。`,`This cycle has ${c.length} slots. After ${S.round} steps, the tracked sticker is at slot ${pos+1}.`);teaching.querySelectorAll('[data-cycle-start]').forEach(b=>b.setAttribute('aria-pressed',String(selectedCycle().includes(Number(b.dataset.cycleStart)))));}
  function update(){
   const restored=S.round>0&&!S.phase&&M.same(M.at(S.base,p,S.round),S.base);
   lab.dataset.round=String(S.round);lab.dataset.order=String(N);lab.dataset.returned=String(restored);
   lab.querySelector('[data-round]').textContent=t(`已完成 ${S.round} 轮`,`Completed ${S.round} rounds`);
   lab.querySelector('[data-return]').textContent=t(`共同回归 N = ${N}`,`Common return N = ${N}`);
   lab.querySelector('[data-verdict]').textContent=restored?t('回到所选起点','Back at the chosen start'):S.phase?t('正在执行一轮…','Executing one round…'):S.round===0?t('这是本轮实验的起点','The start of this experiment'):t('继续重复同一套动作','Repeat the same sequence');
   lab.querySelector('[data-play]').textContent=S.running?t('暂停','Pause'):S.phase?t('继续到回归','Resume to return'):t('连续到回归','Repeat until return');
   lab.querySelector('[data-once]').disabled=!!S.phase;
   lab.querySelector('[data-start]').textContent=S.scrambled?t('换成复原起点','Start from solved'):t('换成打乱起点','Start from scrambled');
   lab.querySelector('[data-labels]').setAttribute('aria-pressed',String(S.numbers));
   lab.querySelector('.rubik-start-label').textContent=S.scrambled?t('起点：打乱状态','Start: scrambled state'):t('起点：复原状态','Start: solved state');
   lab.querySelectorAll('[data-rubik-word]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.rubikWord===S.recipe)));
   const slider=teaching.querySelector('[data-round-range]');if(slider)slider.value=String(S.round);updateCycle();
   const states=[S.base,M.apply(p,S.base)];teaching.querySelectorAll('[data-model-state]').forEach(net=>net.querySelectorAll('[data-net-slot]').forEach(cell=>{cell.style.backgroundColor=M.slots[states[Number(net.dataset.modelState)][Number(cell.dataset.netSlot)]].color;}));
  }
  lab.querySelectorAll('[data-rubik-stage]').forEach(b=>b.onclick=()=>{S.stage=Number(b.dataset.rubikStage);showTeaching();update();});
  lab.querySelectorAll('[data-rubik-word]').forEach(b=>b.onclick=()=>setRecipe(b.dataset.rubikWord));
  on('form','submit',e=>{e.preventDefault();const error=lab.querySelector('.rubik-input-error');try{setRecipe(lab.querySelector('input').value);error.hidden=true;}catch{error.hidden=false;error.textContent=t("请用空格分隔 R L U D F B，可加 ' 或 2；每轮最多 40 步。","Use space-separated R L U D F B, with optional ' or 2; at most 40 moves.");}});
  on('[data-once]','click',()=>startRound('one'));on('[data-play]','click',()=>{if(S.running)S.running=false;else startRound('all');update();});on('[data-reset]','click',()=>seek(0));
  on('[data-start]','click',()=>{stop();S.scrambled=!S.scrambled;S.base=S.scrambled?M.apply(M.word("F R U2 L' D B2 R' U F2 D' L B"),M.identity()):M.identity();S.round=0;update();});
  on('[data-labels]','click',()=>{S.numbers=!S.numbers;update();});
  canvas.addEventListener('pointerdown',e=>{drag={x:e.clientX,y:e.clientY,startX:e.clientX,startY:e.clientY};canvas.setPointerCapture(e.pointerId);});
  canvas.addEventListener('pointermove',e=>{if(!drag)return;S.yaw+=(e.clientX-drag.x)*.009;S.pitch=Math.max(-1.35,Math.min(1.35,S.pitch+(e.clientY-drag.y)*.008));drag.x=e.clientX;drag.y=e.clientY;});
  canvas.addEventListener('pointerup',e=>{if(drag&&Math.hypot(e.clientX-drag.startX,e.clientY-drag.startY)<7&&!S.phase){const r=canvas.getBoundingClientRect(),scale=Math.min(r.width/900,r.height/620),x=(e.clientX-r.left-(r.width-900*scale)/2)/scale,y=(e.clientY-r.top-(r.height-620*scale)/2)/scale;const tile=hit.filter(q=>Math.hypot(q.center[0]-x,q.center[1]-y)<38).sort((a,b)=>Math.hypot(a.center[0]-x,a.center[1]-y)-Math.hypot(b.center[0]-x,b.center[1]-y))[0];if(tile){S.selected=M.power(p,-S.round)[tile.index];update();}}drag=null;});
  const cam=v=>M.rotate(M.rotate(v,1,S.yaw),0,S.pitch);
  const project=v=>{const q=cam(v),k=9/(9-q[2]);return[450+q[0]*116*k,260-q[1]*116*k,q[2]];};
  function polygon(points){ctx.beginPath();points.forEach((v,i)=>ctx[i?'lineTo':'moveTo'](v[0],v[1]));ctx.closePath();}
  function draw(now){
   const dt=Math.min(50,now-last);last=now;
   if(S.running&&S.phase){const phase=S.phase;phase.elapsed+=dt;const duration=matchMedia('(prefers-reduced-motion: reduce)').matches?1:540;let completed=false;
    if(phase.elapsed>=duration){phase.before=M.apply(M.tokenInfo(phase.tokens[phase.index]).permutation,phase.before);phase.elapsed=0;phase.index++;if(phase.index===phase.tokens.length){S.round++;S.phase=null;if(S.mode==='one'||S.round===N)S.running=false;else S.phase={tokens:M.parse(S.recipe),index:0,elapsed:0,before:M.at(S.base,p,S.round)};completed=true;}if(completed)update();}
   }
   const phase=S.phase,info=phase?M.tokenInfo(phase.tokens[phase.index]):null,duration=matchMedia('(prefers-reduced-motion: reduce)').matches?1:540,u=phase?Math.min(1,phase.elapsed/duration):0,angle=info?info.angle*u*u*(3-2*u):0,state=endpoint();
   const moveLabel=lab.querySelector('.rubik-move-label'),moveText=info?`${S.recipe}  ·  ${info.token}`:S.recipe;if(moveLabel.textContent!==moveText)moveLabel.textContent=moveText;
   ctx.clearRect(0,0,900,620);const bg=ctx.createRadialGradient(450,240,10,450,260,510);bg.addColorStop(0,'#193137');bg.addColorStop(.65,'#0b151c');bg.addColorStop(1,'#070d12');ctx.fillStyle=bg;ctx.fillRect(0,0,900,620);
   for(let i=0;i<23;i++){const x=60+(i*137)%780,y=55+(i*73)%440+Math.sin(now*.00025+i)*9;ctx.save();ctx.translate(x,y);ctx.rotate(i+now*.00004);ctx.fillStyle=M.faces[i%6][4]+'38';ctx.fillRect(-3,-3,6+i%5,6+i%5);ctx.restore();}
   const polys=[];let tracked=state.indexOf(S.base[S.selected]);
   for(let i=0;i<54;i++){const s=M.slots[i],moving=info&&s.p[info.axis]===info.layer,rot=v=>moving?M.rotate(v,info.axis,angle):v,n=rot(s.n),cameraNormal=cam(n);if(cameraNormal[2]<.006)continue;
    const corners=a=>[[-1,-1],[1,-1],[1,1],[-1,1]].map(([x,y])=>project(rot(s.p.map((v,j)=>v+s.n[j]*.501+s.u[j]*x*a+s.v[j]*y*a))));
    const outer=corners(.497),inner=corners(.431),center=project(rot(s.p.map((v,j)=>v+s.n[j]*.512)));
    polys.push({index:i,outer,inner,center,depth:center[2],color:M.slots[state[i]].color,light:.58+.42*Math.max(0,(cameraNormal[0]*-.25+cameraNormal[1]*.6+cameraNormal[2])/.95),tracked:i===tracked});
   }
   polys.sort((a,b)=>a.depth-b.depth);
   ctx.save();ctx.globalAlpha=.14;ctx.translate(0,673.2);ctx.scale(1,-.36);for(const q of polys){polygon(q.outer);ctx.fillStyle='#080b10';ctx.fill();polygon(q.inner);ctx.fillStyle=q.color;ctx.fill();}ctx.restore();
   ctx.fillStyle='#d8b46914';ctx.beginPath();ctx.ellipse(450,495,238,19,0,0,Math.PI*2);ctx.fill();
   for(const q of polys){polygon(q.outer);ctx.fillStyle='#090d11';ctx.fill();ctx.strokeStyle='#34424a';ctx.lineWidth=1.2;ctx.stroke();polygon(q.inner);ctx.fillStyle=q.color;ctx.fill();ctx.fillStyle=`rgba(0,0,0,${1-q.light})`;ctx.fill();const sheen=ctx.createLinearGradient(q.inner[0][0],q.inner[0][1],q.inner[2][0],q.inner[2][1]);sheen.addColorStop(0,'#ffffff29');sheen.addColorStop(.45,'#ffffff03');sheen.addColorStop(1,'#00000014');ctx.fillStyle=sheen;ctx.fill();
    if(q.tracked){ctx.strokeStyle='#fff0b4';ctx.lineWidth=4;ctx.shadowColor='#f8ce71';ctx.shadowBlur=17;ctx.stroke();ctx.shadowBlur=0;}
    if(S.numbers){ctx.font='600 20px system-ui';ctx.textAlign='center';ctx.textBaseline='middle';ctx.lineWidth=3;ctx.strokeStyle='#0008';ctx.strokeText(String(state[q.index]+1),q.center[0],q.center[1]);ctx.fillStyle='#fff9e4';ctx.fillText(String(state[q.index]+1),q.center[0],q.center[1]);}
   }
   hit=polys;
   if(alive)raf=requestAnimationFrame(draw);
  }
  inspect=()=>({recipe:S.recipe,round:S.round,order:N,stage:S.stage,playing:S.running,moving:!!S.phase,moveIndex:S.phase?.index??null,turnElapsed:S.phase?.elapsed??0,state:endpoint().slice(),base:S.base.slice(),permutation:p.slice(),returned:lab.dataset.returned==='true'});
  showTeaching();update();raf=requestAnimationFrame(draw);
  return()=>{alive=false;cancelAnimationFrame(raf);drag=null;};
 }
 window.RubikAction={mount,inspect:()=>inspect()};
})();
