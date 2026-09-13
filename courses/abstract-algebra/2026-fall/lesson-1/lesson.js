/* Original interactive teaching companion. All calculations are local. */
(()=>{
  'use strict';
  const M=window.AlgebraLessonMath;
  const $=id=>document.getElementById(id);
  const scene=$('scene');
  const colors=['#2b8a77','#b46c34','#527fb4','#8d68a9','#a65061','#607e41'];
  const soft=['#e3efe5','#f7eadb','#e6edf5','#eee7f4','#f3e6e9','#eaf0de'];
  let current=0,animationToken=0,onResize=()=>{};
  const reduced=()=>matchMedia('(prefers-reduced-motion: reduce)').matches;
  const sections=[
    {id:'relation',nav:'等价关系',kicker:'01 / RELATION',title:'何时可以说<br>“它们一样”？',lead:'等价不是完全相同，而是在约定的标准下，忽略我们不关心的差别。三条性质保证分类不会自相矛盾。',formula:'反身 · 对称 · 传递',definition:'关系是有序对的集合 R ⊆ S × S。<br>等价关系同时满足这三条性质。',prompt:'删掉一个关系，再看哪条性质失效。为什么每个元素都必须和自己等价？',source:'教材 §1.1 · 定义 1.1.1—1.1.4<br>定理 1.1.1 · 例 9',label:'关系实验室 / S = {a, b, c}',render:renderRelation},
    {id:'quotient',nav:'等价类',kicker:'02 / QUOTIENT SET',title:'把一整类<br>看成一个点。',lead:'改变观察的尺度：先看整数，再按余数分类，最后让每个等价类成为新集合中的一个元素。',formula:'[a] = {a + km : k ∈ ℤ}',definition:'a ∼ b ⇔ m 整除 a − b。<br>ℤ / ∼ = {[0], …, [m − 1]}，记作 ℤₘ。',prompt:'将视角推到“商集”，再更换代表元：数字变了，所在的类会改变吗？',source:'教材 §1.1 · 定义 1.1.3 · 例 5、7<br>图中仅展示有限窗口，整数集与各类均无限。',label:'从整数到剩余类 / 连续改变视角',render:renderQuotient},
    {id:'operation',nav:'定义运算',kicker:'03 / WELL-DEFINED',title:'换一个代表，<br>结果还一样吗？',lead:'要在商集上做运算，结果必须由“类”决定。选谁来代表这个类，不应影响最后得到的类。',formula:'[a] + [b] = [a + b]',definition:'良定义：若 [a] = [a′]、[b] = [b′]，则 [a + b] = [a′ + b′]。',prompt:'独立改变两个代表元。计算结果的整数可能不同，但落入的剩余类保持不变。',source:'教材 §1.2 · 定义 1.2.1 · 例 2<br>商集只是集合；指定合适运算后才继续讨论群。',label:'代表元实验 / 固定在 ℤ₅ 中',render:renderOperation},
    {id:'symmetry',nav:'对称与群',kicker:'04 / SYMMETRY',title:'让“做一件事”<br>成为一个元素。',lead:'群的元素也可以是变换。把两次操作接起来，就得到它们的乘积。交换操作的先后次序，结果未必相同。',formula:'B ∘ A：先 A，后 B',definition:'r：逆时针旋转 120°。<br>s：沿经过顶点 1 的竖直轴反射。<br>六个变换：e, r, r², s, rs, r²s。',prompt:'选 A = r、B = s，播放两种顺序。跟踪顶点的编号，而不只是三角形的轮廓。',source:'作为 §1.2 群概念的几何补充例子<br>编号仅用于追踪；对称指未着色三角形的对称。',label:'三角形的对称 / 群 D₃，|D₃| = 6',render:renderSymmetry},
    {id:'axioms',nav:'群的公理',kicker:'05 / GROUP AXIOMS',title:'同一个集合，<br>换运算就不同。',lead:'先检查运算是否处处有唯一结果且留在集合内，再检查结合律、单位元和每个元素的逆元。交换律是额外条件。',formula:'(ab)c = a(bc)<br>ea = ae = a<br>aa⁻¹ = a⁻¹a = e',definition:'G 必须非空。“封闭”属于代数运算的要求；其余三条是教材的 G1—G3。',prompt:'比较 ℤ₆ 的加法与乘法。再试试“删掉 [0]”：这次连哪一关都过不了？',source:'教材 §1.2 · 定义 1.2.2 · 例 3—10<br>表格按“行元素 ∘ 列元素”读取。',label:'群表实验室 / 点击一格读取乘积',render:renderAxioms},
    {id:'properties',nav:'基本性质',kicker:'06 / REASONING',title:'每一步等式，<br>都要有理由。',lead:'单位元和逆元为什么唯一？逆运算为什么要倒着做？消去律又从哪里来？从公理出发，一步一步推出来。',formula:'(ab)⁻¹ = b⁻¹a⁻¹',definition:'逆元把操作撤销。若先做 b 再做 a，就要先撤销 a，再撤销 b。',prompt:'点“下一步”，尝试先说出所用公理，再查看理由。注意全过程没有擅自交换因子。',source:'教材 §1.2 · 定理 1.2.1—1.2.2<br>先理解这些基本性质，再练习独立证明。',label:'证明工作台 / 等式与依据同步',render:renderProperties},
    {id:'order',nav:'元素的阶',kicker:'07 / ELEMENT ORDER',title:'重复多少次，<br>才第一次回到原点？',lead:'固定一个群元素，反复进行同一种运算。第一次回到单位元所需的正整数次数，就是这个元素的阶。',formula:'ord(a) = min{k ≥ 1 : aᵏ = e}',definition:'不存在这样的正整数时，称 a 为无限阶。<br>加群中应写 ka = 0，而不是普通数的乘方。',prompt:'在 (ℤ₆, +) 中比较 [1]、[2]、[3]。群一直有 6 个元素，但它们各自多久回来？',source:'按主页第一讲“元素的阶”目标提前引入<br>结合 §1.2 的方幂，后续 §1.5 系统学习。',label:'重复运算 / 从单位元出发',render:renderOrder},
    {id:'check',nav:'课末自测',kicker:'08 / CHECK YOUR UNDERSTANDING',title:'会操作之后，<br>能解释了吗？',lead:'用六个短问题检查本讲的关键概念。每题都有理由，答错也可以直接看到误区在哪里。',formula:'例子 → 定义 → 理由',definition:'学习目标：能辨认等价关系、解释商集、验证群公理、使用基本性质、计算元素的阶。',prompt:'先自己判断，再选择答案。把不熟悉的概念带回前面的实验重新验证。',source:'本讲配套原创检查题<br>建议课后完成教材习题 1-1 的 1、2、4；<br>习题 1-2 的 5、6(1)、10。',label:'第一讲 / 六道概念检查',render:renderQuiz}
  ];
  function svg(content,viewBox='0 0 760 330',label='交互数学图示'){return `<svg viewBox="${viewBox}" role="img" aria-label="${label}">${content}</svg>`;}
  function animate(duration,update){
    const token=++animationToken;
    return new Promise(resolve=>{
      if(reduced()){update(1);resolve(true);return;}
      const start=performance.now();
      function frame(now){if(token!==animationToken){resolve(false);return;}const t=Math.min(1,(now-start)/duration);update(t<.5?2*t*t:1-((-2*t+2)**2)/2);if(t<1)requestAnimationFrame(frame);else resolve(true);}
      requestAnimationFrame(frame);
    });
  }
  const setStatus=(text,bad=false)=>{const el=$('status');if(el){if(el.innerHTML!==text)el.innerHTML=text;el.classList.toggle('bad',bad);}};
  $('chapter-nav').innerHTML=sections.map((s,i)=>`<button type="button" data-section="${i}" aria-current="${i===0?'step':'false'}"><span>${String(i+1).padStart(2,'0')}</span>${s.nav}</button>`).join('');
  function show(i,{focus=false}={}){
    ++animationToken;onResize=()=>{};current=Math.max(0,Math.min(sections.length-1,i));const s=sections[current];
    $('section-kicker').textContent=s.kicker;$('section-title').innerHTML=s.title;$('section-lead').textContent=s.lead;
    $('definition').innerHTML=`<span class="label">核心语言</span><div class="formula">${s.formula}</div><p>${s.definition}</p>`;
    $('prompt').innerHTML=`<b>试着发现</b>${s.prompt}`;$('source-note').innerHTML=s.source;$('experiment-label').textContent=s.label;
    $('chapter-nav').querySelectorAll('button').forEach((b,k)=>b.setAttribute('aria-current',k===current?'step':'false'));
    $('previous').disabled=current===0;$('next').disabled=current===sections.length-1;$('next').textContent=current===sections.length-2?'进入自测 →':'下一节 →';
    $('page-count').textContent=`${String(current+1).padStart(2,'0')} / 08`;
    history.replaceState(null,'','#'+s.id);scene.innerHTML='';s.render();
    if(focus)$('workspace').focus({preventScroll:true});
  }
  $('chapter-nav').addEventListener('click',e=>{const b=e.target.closest('button');if(b)show(Number(b.dataset.section));});
  $('previous').onclick=()=>show(current-1);$('next').onclick=()=>show(current+1);
  document.addEventListener('keydown',e=>{if(e.altKey||e.ctrlKey||e.metaKey||e.shiftKey||e.target.closest('input,select,textarea,button,summary,[contenteditable]'))return;if(e.key==='ArrowRight'||e.key==='ArrowLeft'){e.preventDefault();show(current+(e.key==='ArrowRight'?1:-1),{focus:true});}});
  window.addEventListener('hashchange',()=>{const n=sections.findIndex(s=>s.id===location.hash.slice(1));if(n>=0&&n!==current)show(n);});
  window.addEventListener('resize',()=>onResize());
  $('fullscreen').onclick=async()=>{try{if(document.fullscreenElement)await document.exitFullscreen();else await document.documentElement.requestFullscreen();}catch{document.body.classList.toggle('present');$('fullscreen').textContent=document.body.classList.contains('present')?'退出讲授 ↙':'全屏讲授 ↗';}};
  document.addEventListener('fullscreenchange',()=>{document.body.classList.toggle('present',!!document.fullscreenElement);$('fullscreen').textContent=document.fullscreenElement?'退出全屏 ↙':'全屏讲授 ↗';});

  function renderRelation(){
    let R=M.fromBlocks([[0,1],[2]]);const letters=['a','b','c'];
    scene.innerHTML=`<div class="controls"><label>观察例子 <select id="relation-preset"><option value="equivalence">一个等价关系</option><option value="reflexive">只缺反身性</option><option value="symmetric">只缺对称性</option><option value="transitive">只缺传递性</option><option value="custom" disabled>自定义关系</option></select></label><span class="spacer"></span><button type="button" id="repair">补成等价关系</button></div><div class="relation-layout"><div id="relation-graph" class="stage"></div><div id="relation-matrix"></div></div><p class="hint">点击右侧方格：● 表示行元素与列元素有关系，· 表示没有。箭头有方向，自环表示与自己相关。</p><div id="relation-properties" class="property-row"></div><p class="section-small">三个元素的全部五种分类 / 点击查看对应关系</p><div id="partition-options" class="partition-options"></div><div id="status" class="status-strip" role="status" aria-live="polite"></div><details class="mini-proof"><summary>把图形翻译成定义与证明</summary><p>对任意 a, b, c ∈ S：<br>反身性：a ∼ a。<br>对称性：a ∼ b ⇒ b ∼ a。<br>传递性：a ∼ b 且 b ∼ c ⇒ a ∼ c。</p><p><b>从等价关系到分类：</b>若 c ∈ [a] ∩ [b]，对任意 x ∈ [a]，有 x ∼ a、a ∼ c、c ∼ b，由传递性得 x ∼ b，所以 [a] ⊆ [b]。反向同理。因此 [a] = [b]。反身性保证每个元素都在自己的类中；不同的类于是非空、不重、不漏。</p><p><b>从分类到等价关系：</b>规定“两元素在同一类”就是等价。每个元素在自己的类中；同一类的归属是对称的；如果 a、b 同类，b、c 同类，因为 b 只属于一个类，a、c 也同类。三条性质因此都成立。</p></details>`;
    function update(message){
      const result=M.inspectRelation(R);const f=result.failures;
      const P=[[85,172],[210,65],[335,172]];let content=`<defs><marker id="arrow-r" markerWidth="6" markerHeight="6" refX="5" refY="3" orient="auto-start-reverse"><path d="M0 0L6 3L0 6" fill="none" stroke="#668d7e"/></marker></defs>`;
      for(let a=0;a<3;a++)for(let b=0;b<3;b++)if(R[a][b]){
        const [x,y]=P[a],[u,v]=P[b];
        if(a===b)content+=`<path d="M ${x-16} ${y-21} C ${x-57} ${y-76}, ${x+57} ${y-76}, ${x+16} ${y-21}" fill="none" stroke="#668d7e" stroke-width="1.5" marker-end="url(#arrow-r)"/>`;
        else{const dx=u-x,dy=v-y,len=Math.hypot(dx,dy),ox=-dy/len*15,oy=dx/len*15;content+=`<path d="M${x+dx/len*29} ${y+dy/len*29} Q ${(x+u)/2+ox} ${(y+v)/2+oy} ${u-dx/len*32} ${v-dy/len*32}" fill="none" stroke="#668d7e" stroke-width="1.6" marker-end="url(#arrow-r)"/>`;}
      }
      P.forEach(([x,y],a)=>{const c=result.valid?result.blocks.findIndex(b=>b.includes(a)):a;content+=`<circle cx="${x}" cy="${y}" r="28" fill="${soft[c]}" stroke="${colors[c]}" stroke-width="1.5"/><text x="${x}" y="${y+7}" text-anchor="middle" class="math-label" font-size="24" fill="${colors[c]}">${letters[a]}</text>`;});
      $('relation-graph').innerHTML=svg(content,'0 0 420 245',result.valid?'有向关系图：同色节点属于同一等价类':'有向关系图：当前关系不满足全部等价关系性质');
      $('relation-matrix').innerHTML=`<table class="matrix"><caption>行 → 列</caption><thead><tr><th></th>${letters.map(x=>`<th scope="col">${x}</th>`).join('')}</tr></thead><tbody>${R.map((row,a)=>`<tr><th scope="row">${letters[a]}</th>${row.map((v,b)=>`<td><button type="button" data-a="${a}" data-b="${b}" class="${v?'on':''}" aria-pressed="${v}" aria-label="${letters[a]} 与 ${letters[b]} ${v?'有':'没有'}关系，点击切换">${v?'●':'·'}</button></td>`).join('')}</tr>`).join('')}</tbody></table>`;
      const explanations=[f.reflexive?`${letters[f.reflexive[0]]} 与自身无关系`:'每个元素都有自环',f.symmetric?`${letters[f.symmetric[0]]} → ${letters[f.symmetric[1]]} 缺少反向`:'每条箭头都有反向',f.transitive?`${f.transitive.map(a=>letters[a]).join(' → ')} 缺少捷径`:'两步可达也能直接到达'];
      $('relation-properties').innerHTML=['反身性','对称性','传递性'].map((x,i)=>`<div class="property ${Object.values(f)[i]?'fail':''}"><b>${x}</b><em>${Object.values(f)[i]?'✕':'✓'}</em><span>${explanations[i]}</span></div>`).join('');
      $('partition-options').innerHTML=M.partitions3.map((p,i)=>`<button type="button" data-partition="${i}" aria-pressed="${JSON.stringify(M.fromBlocks(p))===JSON.stringify(R)}">${p.map(b=>`{${b.map(a=>letters[a]).join(',')}}`).join(' | ')}</button>`).join('');
      setStatus((message?message+'<br>':'')+(result.valid?`<strong>形成分类。</strong> S / ∼ = { ${result.blocks.map(b=>`{${b.map(a=>letters[a]).join(', ')}}`).join(', ')} }`:'<strong>还不能作为等价关系。</strong> 找到一个反例，就足以否定对应性质。'),!result.valid);
    }
    $('relation-matrix').onclick=e=>{const b=e.target.closest('button');if(!b)return;const a=+b.dataset.a,c=+b.dataset.b;R[a][c]=!R[a][c];$('relation-preset').value='custom';update();$('relation-matrix').querySelector(`[data-a="${a}"][data-b="${c}"]`).focus({preventScroll:true});};
    $('partition-options').onclick=e=>{const b=e.target.closest('button');if(b){R=M.fromBlocks(M.partitions3[+b.dataset.partition]);$('relation-preset').value='equivalence';update();}};
    $('relation-preset').onchange=e=>{R=e.target.value==='reflexive'?[[true,true,false],[true,true,false],[false,false,false]]:e.target.value==='symmetric'?[[true,true,true],[false,true,true],[false,false,true]]:e.target.value==='transitive'?[[true,true,false],[true,true,true],[false,true,true]]:M.fromBlocks([[0,1],[2]]);update();};
    $('repair').onclick=()=>{let before=R.flat().filter(Boolean).length;for(let a=0;a<3;a++){R[a][a]=true;for(let b=0;b<3;b++)R[a][b]=R[b][a]=R[a][b]||R[b][a];}for(let k=0;k<3;k++)for(let a=0;a<3;a++)for(let b=0;b<3;b++)R[a][b]=R[a][b]||(R[a][k]&&R[k][b]);update(`补入 ${R.flat().filter(Boolean).length-before} 个有序对，得到包含原关系的最小等价关系。`);};
    update();
  }

  function renderQuotient(){
    let m=3,t=0,a=1;
    scene.innerHTML=`<div class="controls"><label>模数 m <select id="modulus">${M.range(5).map(i=>`<option value="${i+2}" ${i===1?'selected':''}>${i+2}</option>`).join('')}</select></label><span class="spacer"></span><button id="quotient-play" type="button" class="primary">看一次分类 →</button></div><div id="quotient-graph" class="stage quotient-stage"></div><div class="control-pair"><label>观察尺度 <output id="scale-label">整数</output><input id="quotient-scale" type="range" min="0" max="100" value="0" aria-label="观察尺度：整数到分类到商集"></label><label>代表元 a <output id="representative-value">1</output><input id="representative" type="range" min="-6" max="11" value="1" aria-label="选择代表元"></label></div><div id="quotient-class" class="insight"></div><div id="status" class="status-strip" role="status" aria-live="polite"></div><p class="hint">图示窗口 −6 ≤ a ≤ 11。每一类还向两端无限延伸；压成的点代表整个集合，不代表某个整数。</p>`;
    function draw(){
      const compact=scene.clientWidth<620,W=compact?400:760;
      const values=M.range(18).map(i=>i-6),r=M.mod(a,m),group=Math.min(1,t*2),collapse=Math.max(0,t*2-1);const cx=i=>(compact?40:70)+i*(compact?320:620)/(m-1);let content='';
      for(let i=0;i<m;i++){
        const count=values.filter(v=>M.mod(v,m)===i).length;
        content+=`<rect x="${cx(i)-38}" y="${165-(count*26+28)/2}" width="76" height="${count*26+28}" rx="36" fill="${soft[i]}" opacity="${group*(1-collapse)}"/><text x="${cx(i)}" y="319" text-anchor="middle" font-size="14" fill="${colors[i]}" opacity="${group}">[${i}]</text>`;
      }
      values.forEach((v,i)=>{
        const cl=M.mod(v,m),members=values.filter(w=>M.mod(w,m)===cl),idx=members.indexOf(v);const x0=(compact?30:65)+(i%6)*(compact?68:126),y0=65+Math.floor(i/6)*96;const gx=cx(cl),gy=165+(idx-(members.length-1)/2)*26;const x=x0+(gx-x0)*group,y=(y0+(gy-y0)*group)*(1-collapse)+165*collapse;
        content+=`<g class="group-point" data-integer="${v}" tabindex="0" role="button" aria-label="选择代表元 ${v}，属于 [${cl}] 类" opacity="${1-collapse*.75}"><circle cx="${x}" cy="${y}" r="${v===a?16:13}" fill="${v===a?colors[cl]:soft[cl]}" stroke="${colors[cl]}" stroke-width="${v===a?2:1}"/><text x="${x}" y="${y+5}" font-size="${compact?15:12}" text-anchor="middle" fill="${v===a?'#fff':colors[cl]}" opacity="${1-collapse}">${v}</text></g>`;
      });
      if(collapse>0)for(let i=0;i<m;i++)content+=`<g pointer-events="none" opacity="${collapse}"><circle cx="${cx(i)}" cy="165" r="${i===r?32:26}" fill="${soft[i]}" stroke="${colors[i]}" stroke-width="${i===r?3:1.5}"/><text x="${cx(i)}" y="173" font-size="25" class="math-label" text-anchor="middle" fill="${colors[i]}">[${i}]</text></g>`;
      $('quotient-graph').innerHTML=svg(content,`0 0 ${W} 335`,`模 ${m} 的分类。代表元 ${a} 属于剩余类 [${r}]；商集共有 ${m} 个元素。`);
      $('scale-label').textContent=t<.25?'整数':t<.75?'按余数分类':'商集';$('representative-value').textContent=a;
      $('quotient-class').innerHTML=`<span class="formula">[${a}] = [${r}] = { …, ${r-2*m}, ${r-m}, ${r}, ${r+m}, ${r+2*m}, … }</span><br>同一类可以有不同的名字：[${a}] 与 [${r}] 是同一个集合。`;
      setStatus(`整数有无穷多个，模 ${m} 的等价类恰好有 <strong>${m} 个</strong>。商集 ℤ${['₀','₁','₂','₃','₄','₅','₆'][m]} 的元素是这些类。`);
    }
    $('modulus').onchange=e=>{m=+e.target.value;draw();};$('representative').oninput=e=>{a=+e.target.value;draw();};
    $('quotient-scale').oninput=e=>{++animationToken;t=+e.target.value/100;draw();};
    const choose=e=>{const el=e.target.closest('[data-integer]');if(el){a=+el.dataset.integer;$('representative').value=a;draw();}};
    $('quotient-graph').onclick=choose;$('quotient-graph').onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();choose(e);}};
    $('quotient-play').onclick=async()=>{t=0;const control=$('quotient-scale');await animate(1800,p=>{t=p;control.value=Math.round(100*p);draw();});};onResize=draw;draw();
  }

  function renderOperation(){
    let k=0,l=0,multiply=false;const r=2,s=4,m=5;
    scene.innerHTML=`<div class="controls"><label>类上的运算 <select id="operation-kind"><option value="add">剩余类加法</option><option value="multiply">剩余类乘法</option></select></label></div><div class="rep-area"><div class="rep-box"><small>第一个类固定为 [2]</small><div id="rep-a" class="big-number"></div><p>a = 2 + 5k</p></div><div class="rep-box b"><small>第二个类固定为 [4]</small><div id="rep-b" class="big-number"></div><p>b = 4 + 5ℓ</p></div></div><div class="control-pair"><label>改变代表元 a <output id="k-output"></output><input id="rep-k" type="range" min="-3" max="3" value="0"></label><label>改变代表元 b <output id="l-output"></output><input id="rep-l" type="range" min="-3" max="3" value="0"></label></div><div id="rep-result" class="rep-result"></div><div id="operation-proof" class="insight"></div><div id="status" class="status-strip" role="status" aria-live="polite"></div>`;
    function draw(){const a=r+m*k,b=s+m*l,res=multiply?a*b:a+b,canonical=multiply?r*s:r+s,op=multiply?'×':'+';
      $('rep-a').textContent=a;$('rep-b').textContent=b;$('k-output').textContent=`k = ${k}`;$('l-output').textContent=`ℓ = ${l}`;
      $('rep-result').innerHTML=`<div class="formula">${a<0?'('+a+')':a} ${op} ${b<0?'('+b+')':b} = ${res} <span style="color:#9ca997">↦</span> <strong style="color:var(--pine)">[${M.mod(res,m)}]</strong></div><p>[2] ${op} [4] = [${canonical}] = [${M.mod(canonical,m)}]，与 k、ℓ 的取值无关。</p>`;
      $('operation-proof').innerHTML=multiply?'<b>一般的理由</b><br>若 a′ = a + 5k，b′ = b + 5ℓ，则<br><span class="formula">a′b′ − ab = 5(kb + ℓa + 5kℓ)</span><br>差仍是 5 的倍数，所以乘积在同一类中。':'<b>一般的理由</b><br>若 a′ = a + 5k，b′ = b + 5ℓ，则<br><span class="formula">(a′ + b′) − (a + b) = 5(k + ℓ)</span><br>差是 5 的倍数，所以和在同一类中。';
      setStatus(`这次计算与标准代表的结果相差 ${res-canonical} = 5 × (${(res-canonical)/m})。<strong>变的是代表，不变的是结果所属的类。</strong>`);
    }
    $('rep-k').oninput=e=>{k=+e.target.value;draw();};$('rep-l').oninput=e=>{l=+e.target.value;draw();};$('operation-kind').onchange=e=>{multiply=e.target.value==='multiply';draw();};draw();
  }

  function renderSymmetry(){
    let A=1,B=3,busy=false;
    const names=['e · 不动','r · 旋转 120°','r² · 旋转 240°','s · 竖轴反射','rs · 先 s 后 r','r²s · 先 s 后 r²'];
    scene.innerHTML=`<div class="two-selects"><label>操作 A<select id="sym-a">${names.map((n,i)=>`<option value="${i}" ${i===A?'selected':''}>${n}</option>`).join('')}</select></label><label>操作 B<select id="sym-b">${names.map((n,i)=>`<option value="${i}" ${i===B?'selected':''}>${n}</option>`).join('')}</select></label></div><div id="symmetry-graph" class="stage symmetry-stage"></div><div id="sym-readout" class="action-readout"></div><div class="controls"><button type="button" id="sym-play" class="primary">同时播放两种顺序</button><span id="sym-step" class="hint" role="status" aria-live="polite"></span></div><div class="symmetry-legend"><span>虚线：初始位置</span><span>1 / 2 / 3：跟踪顶点</span><span>复合记号统一先右后左</span></div><div id="status" class="status-strip" role="status" aria-live="polite"></div><details class="mini-proof"><summary>为什么这六个变换构成群？</summary><p>任意两个三角形的对称复合后，仍是三角形的对称；函数复合满足结合律；e 什么也不改变；旋转和反射都可以撤销，所以每个变换都有逆元。这里用动作解释公理，正式的群定义见下一节。过渡帧用于展示运动，只有每一步的端点表示列出的六个群元素。</p></details>`;
    const base=M.range(3).map(i=>[-92*Math.sin(i*2*Math.PI/3),-92*Math.cos(i*2*Math.PI/3)]);
    const positions=g=>M.range(3).map(i=>base[M.d3apply(g,i)]);
    function triangle(points,cx){const cy=133;let s=`<path d="${base.map(([x,y],i)=>`${i?'L':'M'}${x+cx},${y+cy}`).join('')}Z" fill="none" stroke="#b9c9bd" stroke-dasharray="5 6" stroke-width="1.3"/><path d="${points.map(([x,y],i)=>`${i?'L':'M'}${x+cx},${y+cy}`).join('')}Z" fill="#dcebe255" stroke="#547f6d" stroke-width="1.6"/>`;
      points.forEach(([x,y],i)=>{s+=`<circle cx="${cx+x}" cy="${cy+y}" r="19" fill="${colors[i]}"/><text x="${cx+x}" y="${cy+y+6}" text-anchor="middle" font-size="19" fill="#fff">${i+1}</text>`;});return s;}
    function draw(left=positions(M.d3mul(B,A)),right=positions(M.d3mul(A,B))){$('symmetry-graph').innerHTML=svg(`<path d="M320 35V240" stroke="#e1e6dc"/>${triangle(left,160)}${triangle(right,480)}<text x="160" y="261" text-anchor="middle" font-size="17" fill="#61736c">先 A，后 B</text><text x="480" y="261" text-anchor="middle" font-size="17" fill="#61736c">先 B，后 A</text>`,'0 0 640 285','左右三角形按两种顺序应用变换，编号与颜色共同追踪三个顶点');}
    function update(){const ba=M.d3mul(B,A),ab=M.d3mul(A,B);$('sym-readout').innerHTML=`<div>${M.d3labels[B]} ∘ ${M.d3labels[A]} = ${M.d3labels[ba]}<small>左图的总变换</small></div><div>${M.d3labels[A]} ∘ ${M.d3labels[B]} = ${M.d3labels[ab]}<small>右图的总变换</small></div>`;
      setStatus(ba===ab?'<strong>这两个操作可交换。</strong> 这只说明当前这一对相等；要证明群交换，需对所有元素对成立。':'<strong>两种顺序得到不同结果。</strong> 因而 D₃ 不是交换群；但它仍然满足结合律。',false);draw();}
    function transformed(points,g,p){
      const flip=g>=3,k=g%3;let fp=flip?(k?Math.min(1,2*p):p):0,rp=flip&&k?Math.max(0,2*p-1):p;
      const theta=2*Math.PI*k/3*rp,c=Math.cos(theta),s=Math.sin(theta);
      return points.map(([x,y])=>{const xx=x*(flip?Math.cos(Math.PI*fp):1);return [c*xx+s*y,-s*xx+c*y];});
    }
    const setBusy=v=>{busy=v;$('sym-a').disabled=v;$('sym-b').disabled=v;$('sym-play').disabled=v;};
    $('sym-play').onclick=async()=>{
      if(busy)return;setBusy(true);const route=current;draw(base,base);$('sym-step').textContent='第 1 步：左边做 A，右边做 B';
      if(!await animate(1000,p=>draw(transformed(base,A,p),transformed(base,B,p))))return;
      if(current!==route)return;$('sym-step').textContent='第 2 步：左边再做 B，右边再做 A';
      const left=positions(A),right=positions(B);
      if(!await animate(1000,p=>draw(transformed(left,B,p),transformed(right,A,p))))return;
      if(current!==route)return;update();$('sym-step').textContent='比较两个终态中的顶点编号';setBusy(false);
    };
    $('sym-a').onchange=e=>{A=+e.target.value;$('sym-step').textContent='';update();};$('sym-b').onchange=e=>{B=+e.target.value;$('sym-step').textContent='';update();};update();
  }

  function renderAxioms(){
    let key='add6',selected=[2,3];
    scene.innerHTML=`<div class="controls"><label>集合与运算 <select id="group-model"><option value="add6">ℤ₆ · 加法</option><option value="mul6">ℤ₆ · 乘法</option><option value="nonzero6">ℤ₆ 去掉 [0] · 乘法</option><option value="unit5">U(5) · 乘法</option><option value="unit8">U(8) · 乘法</option><option value="d3">D₃ · 变换复合</option><option value="subtract3">ℤ₃ · 减法</option></select></label></div><div class="axiom-layout"><div><div id="cayley"></div><p class="hint">读法：行在左，列在右。橙色细框标出结果等于单位元的格子。</p></div><div id="axiom-checks" class="axiom-checks"></div></div><div id="table-readout" class="insight"></div><p id="example-note" class="hint example-note"></p><div id="status" class="status-strip" role="status" aria-live="polite"></div><details class="mini-proof"><summary>再看三个无限集合中的典型例子</summary><p><b>(ℤ, +)</b> 是交换群：单位元为 0，n 的逆元是 −n。<br><b>(ℚ ∖ {0}, ×)</b> 是交换群：单位元为 1，a/b 的逆元是 b/a。<br><b>GLₙ(ℝ)</b> 是可逆实矩阵在乘法下构成的群：单位元为 I，逆元为逆矩阵；n ≥ 2 时一般不交换。<br><b>(ℤ, ×)</b> 不是群，例如 2 的倒数不在 ℤ 中。仅说“整数是群”不完整，还必须指定运算。</p></details>`;
    function update(){
      const model=M.model(key),data=M.inspectOperation(model),E=model.elements,fmt=model.label,op=model.op;
      if(!E.includes(selected[0])||!E.includes(selected[1]))selected=[E[0],E[0]];
      $('cayley').innerHTML=`<table class="cayley"><caption class="sr-only">${model.name} 的运算表</caption><thead><tr><th scope="col">${model.opSymbol}</th>${E.map(b=>`<th scope="col">${fmt(b)}</th>`).join('')}</tr></thead><tbody>${E.map(a=>`<tr><th scope="row">${fmt(a)}</th>${E.map(b=>{const c=op(a,b);return `<td><button type="button" data-left="${a}" data-right="${b}" aria-label="${fmt(a)} ${model.opSymbol} ${fmt(b)} = ${fmt(c)}" aria-pressed="${selected[0]===a&&selected[1]===b}" class="${c===data.identity?'inverse ':''}${!E.includes(c)?'outside ':''}${selected[0]===a&&selected[1]===b?'selected':''}" style="--cell:${soft[Math.max(0,E.indexOf(c))%soft.length]}">${fmt(c)}</button></td>`;}).join('')}</tr>`).join('')}</tbody></table>`;
      const missing=E.filter((a,i)=>data.inverses[i]===undefined).map(fmt).join('、');
      let associativityText=data.associative===null?'不是内部运算，先解决封闭性':data.associative?'全部 '+E.length**3+' 个三元组均满足':'存在不满足结合律的三元组';
      const checks=[['封闭性',data.closed,data.closed?'每个有序对都有唯一的集合内结果':`${fmt(data.closureWitness[0])} ${model.opSymbol} ${fmt(data.closureWitness[1])} = ${fmt(data.closureWitness[2])} 不在集合内`],['结合律',data.associative,associativityText],['单位元',data.identity!==undefined,data.identity!==undefined?`双侧单位元是 ${fmt(data.identity)}`:'找不到对所有元素均有效的双侧单位元'],['每元有逆',data.allInverses,data.allInverses===null?'尚无单位元，不能据此定义逆元':data.allInverses?'每个元素都能从两侧还原单位元':`${missing} 无逆元`]];
      $('axiom-checks').innerHTML=checks.map(([name,pass,note])=>`<div class="axiom-check"><b>${name}</b><span class="${pass===false?'no':''}">${pass===null?'— 待定义':pass?'✓ 成立':'✕ 不成立'}</span><small>${note}</small></div>`).join('');
      const [a,b]=selected,c=op(a,b);let detail=E.includes(c)?'结果仍在所选集合内。':'结果不在所选集合内，因此不封闭。';if(c===data.identity)detail+=` ${fmt(a)} 与 ${fmt(b)} ${op(b,a)===data.identity?'互为双侧逆元。':'只满足当前方向的等式。'}`;
      $('table-readout').innerHTML=`<div class="formula">${model.format(a,b,c)}</div>${detail}`;$('example-note').textContent=model.note;
      let status=data.isGroup?`<strong>是群。</strong> ${data.commutative?'也是交换群：表关于主对角线对称。':'不是交换群：例如 r ∘ s ≠ s ∘ r。'}`:'<strong>不是群。</strong> 必须同时满足定义的全部要求。';
      if(data.associativeWitness){const [x,y,z,left,right]=data.associativeWitness;status+=`<br>反例：(${fmt(x)} − ${fmt(y)}) − ${fmt(z)} = ${fmt(left)}；${fmt(x)} − (${fmt(y)} − ${fmt(z)}) = ${fmt(right)}。`;}
      setStatus(status,!data.isGroup);
    }
    $('group-model').onchange=e=>{key=e.target.value;selected=key==='nonzero6'?[2,3]:key==='mul6'?[0,1]:key==='unit5'?[2,3]:key==='d3'?[1,3]:[M.model(key).elements[0],M.model(key).elements[0]];update();};
    $('cayley').onclick=e=>{const b=e.target.closest('button');if(b){selected=[+b.dataset.left,+b.dataset.right];update();$('cayley').querySelector(`[data-left="${selected[0]}"][data-right="${selected[1]}"]`).focus({preventScroll:true});}};update();
  }

  function renderProperties(){
    let chosen=0,step=0;
    const proofs=[
      {name:'单位元唯一',assumption:'设 e 和 f 都是 G 的双侧单位元。',goal:'结论：e = f',steps:[['e','从 e 开始。'],['e = ef','f 是右单位元，所以 ef = e。'],['e = ef = f','e 是左单位元，所以 ef = f。单位元只能有一个。']]},
      {name:'逆元唯一',assumption:'设 b 和 c 都是 a 的逆元，即 ab = ba = ac = ca = e。',goal:'结论：b = c',steps:[['b','从 b 开始。'],['b = be','右侧乘单位元。'],['b = b(ac)','因为 ac = e。'],['b = (ba)c','只移动括号：结合律。'],['b = ec','因为 ba = e。'],['b = c','左侧单位元不改变 c。逆元唯一。']]},
      {name:'乘积的逆',assumption:'对任意 a, b ∈ G，提出候选逆元 b⁻¹a⁻¹，并检验两侧。',goal:'结论：(ab)⁻¹ = b⁻¹a⁻¹',steps:[['(ab)(b⁻¹a⁻¹)','把候选逆元接在 ab 右侧。'],['a(bb⁻¹)a⁻¹','结合律；因子的顺序未变。'],['aea⁻¹ = aa⁻¹ = e','先消去 b，再消去 a。'],['(b⁻¹a⁻¹)(ab)','还要检查另一侧。'],['b⁻¹(a⁻¹a)b = b⁻¹eb = e','结合律与逆元性质给出单位元。'],['(ab)⁻¹ = b⁻¹a⁻¹','两侧都还原 e，再用逆元唯一性。']]},
      {name:'消去律',assumption:'设 ab = ac。在等式两侧同时左乘 a⁻¹。',goal:'结论：b = c；右消去同理',steps:[['ab = ac','已知条件。'],['a⁻¹(ab) = a⁻¹(ac)','两边同一侧乘同一个元素。'],['(a⁻¹a)b = (a⁻¹a)c','结合律。'],['eb = ec','使用 a⁻¹a = e。'],['b = c','使用单位元性质，得到左消去律。']]},
      {name:'解群方程',assumption:'对给定 a, b ∈ G，分别求解 ax = b 和 ya = b。',goal:'x = a⁻¹b；y = ba⁻¹',steps:[['ax = b','先解未知元在右侧的方程。'],['a⁻¹(ax) = a⁻¹b','左乘 a⁻¹，抵消位于左侧的 a。'],['x = a⁻¹b','结合律和单位元性质；代回检验成立。'],['ya = b','再解未知元在左侧的方程。'],['(ya)a⁻¹ = ba⁻¹','这次要右乘 a⁻¹。'],['y = ba⁻¹','代回检验成立；消去律保证两个解各自唯一。']]}
    ];
    scene.innerHTML=`<div id="proof-tabs" class="controls proof-options"></div><p id="proof-assumption" class="proof-conditions"></p><div id="proof-board" class="proof-board stage" aria-live="polite"></div><div class="controls"><button type="button" id="proof-back">← 上一步</button><button type="button" id="proof-next" class="primary">下一步 →</button><span id="proof-count" class="hint"></span></div><div id="status" class="status-strip"></div><details class="mini-proof"><summary>另外两条需要记住的运算规则</summary><p>逆元的逆还是自己：(a⁻¹)⁻¹ = a，因为 a 和 a⁻¹ 互为逆元。<br>同一个元素的幂满足 aᵐaⁿ = aᵐ⁺ⁿ、(aᵐ)ⁿ = aᵐⁿ。但对于不同元素，(ab)ⁿ = aⁿbⁿ 一般需要 ab = ba；不能仅凭结合律这样拆开。</p></details>`;
    function update(){const p=proofs[chosen];$('proof-tabs').innerHTML=proofs.map((x,i)=>`<button type="button" data-proof="${i}" aria-pressed="${i===chosen}">${x.name}</button>`).join('');$('proof-assumption').textContent=p.assumption;
      $('proof-board').innerHTML=`<div class="label">${p.goal}</div><div class="expression">${p.steps[step][0]}</div><div class="reason">${p.steps[step][1]}</div><div class="proof-track" aria-hidden="true">${p.steps.map((_,i)=>`<span class="${i<=step?'done':''}"></span>`).join('')}</div>`;
      $('proof-back').disabled=step===0;$('proof-next').disabled=step===p.steps.length-1;$('proof-count').textContent=`${step+1} / ${p.steps.length}`;
      setStatus(step===p.steps.length-1?'<strong>证明完成。</strong> 回顾刚才哪些地方用了结合律、单位元或逆元。':'<strong>先预测，再翻一步。</strong> 当前的等式能用哪条公理继续化简？');
    }
    $('proof-tabs').onclick=e=>{const b=e.target.closest('button');if(b){chosen=+b.dataset.proof;step=0;update();}};$('proof-back').onclick=()=>{step--;update();};$('proof-next').onclick=()=>{step++;update();};update();
  }

  function renderOrder(){
    let key='add6',a=2,k=0,running=false;
    scene.innerHTML=`<div class="order-controls"><label>选择群<select id="order-group"><option value="add6">ℤ₆ · 加法</option><option value="unit5">U(5) · 乘法</option><option value="unit8">U(8) · 乘法</option><option value="d3">D₃ · 变换复合</option><option value="integer">ℤ · 加法（无限群）</option></select></label><label>固定元素 a<select id="order-element"></select></label></div><div id="order-graph" class="stage"></div><div id="cycle-sequence" class="cycle-sequence"></div><div id="order-metrics" class="order-metrics"></div><div class="controls"><button type="button" id="order-step" class="primary">再运算一次 →</button><button type="button" id="order-play">走到第一次返回</button><button type="button" id="order-reset" class="quiet">回到单位元</button></div><div id="status" class="status-strip" role="status" aria-live="polite"></div>`;
    function elements(){const E=key==='integer'?[-2,-1,0,1,2]:M.model(key).elements;if(!E.includes(a))a=E[Math.min(1,E.length-1)];$('order-element').innerHTML=E.map(x=>`<option value="${x}" ${x===a?'selected':''}>${key==='integer'?x:M.model(key).label(x)}</option>`).join('');}
    function draw(progress=0){
      const compact=scene.clientWidth<620;
      const infinite=key==='integer'&&a!==0,model=key==='integer'?null:M.model(key),seq=model?M.cycle(model,a):[0,0],ord=model?seq.length-1:infinite?Infinity:1,fmt=model?model.label:String;
      let s='';
      if(key==='integer'){
        const unit=32,center=380,limit=compact?4:9;for(let j=-limit;j<=limit;j++)s+=`<path d="M${center+j*unit} 139v12" stroke="#a2b4a5"/><text x="${center+j*unit}" y="174" text-anchor="middle" font-size="13" fill="#64766c">${j}</text>`;
        s=`<path d="M50 145H710" stroke="#a2b4a5"/>`+s;
        const val=(k+progress)*a,at=center+val*unit,clamped=Math.max(compact?235:55,Math.min(compact?525:705,at)),outside=Math.abs(val)>limit;
        s+=`<path d="M${center} 145H${clamped}" stroke="${colors[0]}" stroke-width="3"/><circle cx="${clamped}" cy="145" r="${outside?8:18}" fill="${colors[0]}"/><text x="${outside?380:clamped}" y="110" text-anchor="middle" font-size="22" class="math-label" fill="${colors[0]}">${outside?(val<0?'← ':'')+Math.round(val)+'（窗外）'+(val>0?' →':''):Math.round(val)}</text><text x="380" y="230" text-anchor="middle" font-size="13" fill="#64766c">${infinite?(compact?'每步加 a；非零 a 永不返回 0。':'整数轴无限延伸；每一步都朝同一方向，永远不会返回 0。'):'0 + 0 = 0；单位元的阶是 1。'}</text>`;
      }else{
        const E=model.elements,n=E.length,P=E.map((_,i)=>[380+112*Math.sin(2*Math.PI*i/n),139-112*Math.cos(2*Math.PI*i/n)]),idx=x=>E.indexOf(x);const pos=x=>P[idx(x)];
        s+=`<circle cx="380" cy="139" r="112" fill="none" stroke="#e0e6dc"/>`;
        for(let j=1;j<seq.length;j++){const [x,y]=pos(seq[j-1]),[u,v]=pos(seq[j]);const active=j<=k;s+=`<path d="M${x} ${y}L${u} ${v}" fill="none" stroke="${active?colors[0]:'#c6d4c7'}" stroke-width="${active?3:1}" ${active?'':'stroke-dasharray="4 5"'}/>`;}
        E.forEach((x,i)=>{const [cx,cy]=P[i],visited=seq.slice(0,k+1).includes(x),isCurrent=x===seq[k];s+=`<circle cx="${cx}" cy="${cy}" r="20" fill="${isCurrent?colors[0]:visited?soft[0]:'#fffefa'}" stroke="${visited?colors[0]:'#c3d0c2'}" stroke-width="${isCurrent?2:1}"/><text x="${cx}" y="${cy+5}" font-size="15" text-anchor="middle" fill="${isCurrent?'#fff':colors[0]}">${fmt(x)}</text>`;});
        s+=`<text x="380" y="132" text-anchor="middle" class="math-label" font-size="27" fill="#234e40">${key==='add6'?`${k}[${a}]`:`a${['⁰','¹','²','³','⁴','⁵','⁶'][k]||'^'+k}`}</text><text x="380" y="162" text-anchor="middle" font-size="13" fill="#61736c">${k===ord?'第一次返回单位元':k===0?'从单位元出发':'重复同一个元素'}</text>`;
        if(progress>0&&k<ord){const [x,y]=pos(seq[k]),[u,v]=pos(seq[k+1]);s+=`<circle cx="${x+(u-x)*progress}" cy="${y+(v-y)*progress}" r="7" fill="${colors[1]}" stroke="#fffefa" stroke-width="2"/>`;}
      }
      $('order-graph').innerHTML=svg(s,compact?'205 0 350 283':'0 0 760 283',`${key==='integer'?'整数加群':model.name} 中元素 ${fmt(a)} 的重复运算，第 ${k} 步。`);
      $('cycle-sequence').innerHTML=key==='integer'?`0 ${k?`→ ${M.range(k).map(i=>(i+1)*a).join(' → ')}`:''}${infinite?' → …':''}`:seq.map((x,i)=>`${i?'<span aria-hidden="true">→</span>':''}<span class="${i===k?'current':i<k?'visited':'future'}">${fmt(x)}</span>`).join('');
      $('order-metrics').innerHTML=`<div><span>群的阶 |G|</span><b>${key==='integer'?'∞':model.elements.length}</b></div><div><span>元素的阶 ord(a)</span><b>${ord===Infinity?'∞':ord}</b></div>`;
      $('order-step').disabled=running||k>=Math.min(ord,8);$('order-play').disabled=running||ord===Infinity||k>=ord;$('order-reset').disabled=running;
      if(infinite)setStatus(`<strong>非零整数在加群中都是无限阶。</strong> 对正整数 j，总有 j × (${a}) ≠ 0。这是一般证明；图上只演示有限步。`);
      else if(k===ord)setStatus(`<strong>第 ${ord} 次首次返回。</strong> ${key==='add6'?`${ord}[${a}] = [0]`:key==='integer'?'1 × 0 = 0':`${fmt(a)} 的 ${ord} 次幂等于 ${fmt(seq[0])}`}，且此前没有正整数次数能返回。`);
      else setStatus(`从单位元算作第 0 步。${ord===1?'单位元再运算一次就返回。':`固定 a = ${fmt(a)}，只沿这一次重复运算到达的点观察。`}<strong>阶取最小正整数。</strong>`);
    }
    const busy=v=>{running=v;$('order-group').disabled=v;$('order-element').disabled=v;draw();};
    async function one(){busy(true);if(!await animate(450,p=>draw(p)))return false;k++;busy(false);return true;}
    $('order-group').onchange=e=>{key=e.target.value;a=key==='add6'?2:key==='integer'?1:M.model(key).elements[1];k=0;elements();draw();};$('order-element').onchange=e=>{a=+e.target.value;k=0;draw();};
    $('order-step').onclick=one;$('order-reset').onclick=()=>{k=0;draw();};
    $('order-play').onclick=async()=>{const ord=key==='integer'?1:M.cycle(M.model(key),a).length-1;while(k<ord){if(!await one())return;}};
    onResize=()=>draw();elements();draw();
  }

  function renderQuiz(){
    const questions=[
      ['若两个等价类有一个公共元素，它们一定……',['完全相同','只在这个元素处相交','至少一个是空集'],0,'若两个类相交，利用对称性与传递性可证明它们互相包含；所以相同。等价类非空。','relation'],
      ['模 3 分类中，[−1] 与 [2] 是……',['两个不同整数，所以是不同类','同一个类的两种写法','两个相交但不同的类'],1,'−1 − 2 = −3 能被 3 整除。因此 [−1] = [2]；商集的元素是整个类。','quotient'],
      ['在 ℤ₆ 中删去 [0]，剩余元素在乘法下构成群吗？',['构成，非零元素都有逆','构成，乘法满足结合律','不构成，例如 [2][3] = [0] 不在集合内'],2,'首先就不封闭。要得到乘法群，应取与 6 互素的剩余类 U(6) = {[1], [5]}。','axioms'],
      ['r 与 s 不交换，会不会使 D₃ 失去群结构？',['不会；交换律不是群公理','会；所有群都必须交换','只要交换顺序就能修复'],0,'群要求结合律，不要求交换律。(AB)C = A(BC) 只改变括号，不交换 A、B、C 的位置。','symmetry'],
      ['一般的群中，(ab)⁻¹ 等于……',['a⁻¹b⁻¹','b⁻¹a⁻¹','ab'],1,'撤销时要倒序：把 b⁻¹a⁻¹ 分别乘在 ab 的左右两边，都可化为 e。','properties'],
      ['(ℤ₆, +) 中 [2] 的阶是多少？',['6，因为群有 6 个元素','2，因为这个元素叫 [2]','3，因为 [0] → [2] → [4] → [0]'],2,'第 3 次加 [2] 才首次回到 [0]。群的阶是 6；这个元素的阶是 3。','order']
    ];
    let q=0,answers=Array(questions.length).fill(null);
    function draw(){
      if(q===questions.length){const correct=answers.filter((a,i)=>a===questions[i][2]).length;scene.innerHTML=`<div class="quiz-end"><p class="eyebrow">LECTURE 01 / COMPLETED</p><h3>六个问题，串起这一讲。</h3><p>首次作答正确 ${correct} / 6。${correct===6?'接下来试着不用图形，独立写出证明。':'下面列出了适合再看一次的概念。'}</p><ol>${questions.map((x,i)=>`<li>${answers[i]===x[2]?'✓':'↺'} ${sections.find(s=>s.id===x[4]).nav} <a href="#${x[4]}">回到实验 ↗</a></li>`).join('')}</ol><div class="insight">课后建议：教材习题 1-1 的 1、2、4；习题 1-2 的 5、6(1)、10。先独立尝试，再用本页验证直觉。</div><button id="quiz-retry" type="button" class="primary">重新自测</button></div>`;$('quiz-retry').onclick=()=>{q=0;answers=Array(questions.length).fill(null);draw();};return;}
      const [question,options,correct,explanation,anchor]=questions[q],answered=answers[q]!==null;
      scene.innerHTML=`<div class="quiz-progress">问题 ${q+1} / ${questions.length}</div><h3 class="quiz-question">${question}</h3><div class="quiz-options">${options.map((x,i)=>`<button type="button" data-answer="${i}" ${answered?'disabled':''} class="${answered?(i===correct?'correct':i===answers[q]?'incorrect':''):''}"><span style="color:var(--muted);margin-right:12px">${'ABC'[i]}</span>${x}</button>`).join('')}</div><div class="quiz-feedback" role="status" aria-live="polite">${answered?`<b>${answers[q]===correct?'判断正确。':'再看一下关键理由。'}</b>${explanation} <a href="#${anchor}">回到实验 ↗</a>`:'选择后查看理由。'}</div><div class="controls"><button type="button" id="quiz-prev" ${q===0?'disabled':''}>← 上一题</button><button type="button" id="quiz-next" class="primary" ${answered?'':'disabled'}>${q===questions.length-1?'查看学习回顾':'下一题 →'}</button></div>`;
      scene.querySelectorAll('[data-answer]').forEach(b=>b.onclick=()=>{answers[q]=+b.dataset.answer;draw();});$('quiz-prev').onclick=()=>{q--;draw();};$('quiz-next').onclick=()=>{q++;draw();};
    }
    draw();
  }
  const initial=sections.findIndex(s=>s.id===location.hash.slice(1));
  show(initial>=0?initial:0);
})();
