/* Original interactive teaching companion. All calculations are local. */
(()=>{
  'use strict';
  const M=window.AlgebraLessonMath;
  const $=id=>document.getElementById(id);
  const scene=$('scene');
  const colors=['var(--diagram-1,#2b8a77)','var(--diagram-2,#b46c34)','var(--diagram-3,#527fb4)','var(--diagram-4,#8d68a9)','var(--diagram-5,#a65061)','var(--diagram-6,#607e41)'];
  const soft=['var(--diagram-soft-1,#e3efe5)','var(--diagram-soft-2,#f7eadb)','var(--diagram-soft-3,#e6edf5)','var(--diagram-soft-4,#eee7f4)','var(--diagram-soft-5,#f3e6e9)','var(--diagram-soft-6,#eaf0de)'];
  let current=0,animationToken=0,onResize=()=>{};
  const reduced=()=>matchMedia('(prefers-reduced-motion: reduce)').matches;
  const allSections=[
    {id:'relation',nav:'等价关系',kicker:'第 1 节',title:'何时可以说<br>“它们一样”？',lead:'等价不是完全相同，而是在约定的标准下，忽略我们不关心的差别。三条性质保证分类不会自相矛盾。',formula:'a ∼ a<br>a ∼ b ⇒ b ∼ a<br>a ∼ b，b ∼ c ⇒ a ∼ c',definition:'设 S 非空，关系是有序对的集合 R ⊆ S × S。上述三条分别为反身性、对称性和传递性，须对所有 a、b、c ∈ S 成立；满足三条的关系称为等价关系。',prompt:'删掉一个关系，再看哪条性质失效。为什么每个元素都必须和自己等价？',source:'教材 §1.1 · 定义 1.1.1—1.1.4<br>定理 1.1.1 · 例 9',label:'关系图与矩阵 · S = {a, b, c}',render:renderRelation},
    {id:'quotient',nav:'等价类',kicker:'第 2 节',title:'把一整类<br>看成一个点。',lead:'改变观察的尺度：先看整数，再按余数分类，最后让每个等价类成为新集合中的一个元素。',formula:'[a] = {a + km : k ∈ ℤ}',definition:'一般地，[a] = {x ∈ S : x ∼ a}，商集 S / ∼ 是全部等价类组成的集合。这里取整数 m ≥ 2，以 m 整除 a − b 定义整数上的等价关系；商集记作 ℤₘ = {[0], …, [m − 1]}。',prompt:'将视角推到“商集”，再更换代表元：数字变了，所在的类会改变吗？',source:'教材 §1.1 · 定义 1.1.3 · 例 5、7<br>图中仅展示有限窗口，整数集与各类均无限。',label:'整数、等价类与商集',render:renderQuotient},
    {id:'operation',nav:'代数运算',kicker:'第 3 节',title:'换一个代表，<br>结果还一样吗？',lead:'要在商集上做运算，结果必须由“类”决定。选谁来代表这个类，不应影响最后得到的类。',formula:'[a] + [b] = [a + b]',definition:'代数运算是映射 S × S → S：每一对元素必须有唯一且仍在 S 内的结果。剩余类加法还须验证结果与代表元选择无关。',prompt:'独立改变两个代表元。计算结果的整数可能不同，但落入的剩余类保持不变。',source:'教材 §1.2 · 定义 1.2.1 · 例 2<br>商集只是集合；指定合适运算后才继续讨论群。',label:'ℤ₅ 上的剩余类运算',render:renderOperation},
    {id:'symmetry',nav:'对称与群',kicker:'第 4 节',title:'让“做一件事”<br>成为一个元素。',lead:'群的元素也可以是变换。把两次操作接起来，就得到它们的乘积。交换操作的先后次序，结果未必相同。',formula:'B ∘ A：先 A，后 B',definition:'r：逆时针旋转 120°。<br>s：沿经过顶点 1 的竖直轴反射。<br>六个变换：e, r, r², s, rs, r²s。',prompt:'选 A = r、B = s，播放两种顺序。跟踪顶点的编号，而不只是三角形的轮廓。',source:'§1.2 群的例子 · 几何演示<br>编号用于追踪；对称指未着色三角形的对称。',label:'三角形的对称 / 群 D₃，|D₃| = 6',render:renderSymmetry},
    {id:'axioms',nav:'群的公理',kicker:'第 5 节',title:'同一个集合，<br>换运算就不同。',lead:'先检查运算是否处处有唯一结果且留在集合内，再检查结合律、单位元和每个元素的逆元。交换律是额外条件。',formula:'结合律：(ab)c = a(bc)<br>单位元：ea = ae = a<br>逆元：aa⁻¹ = a⁻¹a = e',definition:'设 G 为非空集合，已给定代数运算 G × G → G。结合律须对所有 a、b、c ∈ G 成立；须存在同一个 e ∈ G，使每个 a 满足 ea = ae = a；每个 a ∈ G 都须有 a⁻¹ ∈ G，使 aa⁻¹ = a⁻¹a = e。满足这些条件，(G, ·) 才称为群。',prompt:'比较 ℤ₆ 的加法与乘法。再试试“删掉 [0]”：这次连哪一关都过不了？',source:'教材 §1.2 · 定义 1.2.2 · 例 3—10<br>表格按“行元素 ∘ 列元素”读取。',label:'运算表 · 点击方格查看乘积',render:renderAxioms},
    {id:'properties',nav:'基本性质',kicker:'第 6 节',title:'每一步等式，<br>都要有理由。',lead:'单位元和逆元为什么唯一？逆运算为什么要倒着做？消去律又从哪里来？从公理出发，一步一步推出来。',formula:'(ab)⁻¹ = b⁻¹a⁻¹',definition:'逆元把操作撤销。若先做 b 再做 a，就要先撤销 a，再撤销 b。',prompt:'点“下一步”，尝试先说出所用公理，再查看理由。注意全过程没有擅自交换因子。',source:'教材 §1.2 · 定理 1.2.1—1.2.2<br>先理解这些基本性质，再练习独立证明。',label:'群的基本性质 · 逐步证明',render:renderProperties},
    {id:'check',nav:'课末自测',kicker:'第 8 节',title:'会操作之后，<br>能解释了吗？',lead:'用六个短问题检查本讲的关键概念。每题都有理由，答错也可以直接看到误区在哪里。',formula:'例子 → 定义 → 理由',definition:'学习目标：能辨认等价关系、解释商集、验证群公理、使用基本性质、计算元素的阶。',prompt:'先自己判断，再选择答案。把不熟悉的概念带回前面的实验重新验证。',source:'课后练习：习题 1-1 的 1、2、4；<br>习题 1-2 的 5、6(1)、10。',label:'第一讲 / 六道概念检查',render:renderQuiz}
  ];
  const textbookSections={
    '1.1':{title:'等价关系与集合的分类',pages:'1—6',items:['relation','quotient','partition','check'],line:'关系与等价关系 · 等价类 · 集合的分类',path:'关系 → 等价类 → 分类',homework:'习题 1-1：1(1)、2、4、5、6'},
    '1.2':{title:'群的概念',pages:'7—18',items:['operation','axioms','one-sided','symmetry','properties','powers','criteria','check'],line:'代数运算 · 群的定义与例子 · 基本性质 · 方幂 · 判别',path:'运算 → 群 → 性质 → 方幂',homework:'习题 1-2：5、6(2)、10、11、12、13、15'}
  };
  allSections.push(
    {id:'one-sided',nav:'单侧公理',title:'哪些单侧条件足够？',lead:'勾选条件，比较等价定义与最小反例。',formula:'左单位元：ea=a<br>左逆元：∀a ∃b，ba=e',definition:'非空集合与封闭运算为固定前提；所有条件使用同一个候选元素 e。',prompt:'同侧条件与交叉条件的差别在哪里？',source:'扩展 1.2.2 · 参见定理 1.2.3',label:'单侧公理 · 32 种组合',render:()=>window.GroupAxiomLab.render(scene)},
    {id:'partition',nav:'集合的分类',title:'分类与等价关系，<br>是同一件事的两面。',lead:'分类把集合分成非空、不重、不漏的若干类。规定同一类中的元素等价，就能从分类反过来得到等价关系。',formula:'S = ⋃ Sᵢ<br>Sᵢ ∩ Sⱼ = ∅（i ≠ j）',definition:'每个 Sᵢ 都非空。每个元素恰好属于一类。全部等价类构成的集合记为 S / ∼。',prompt:'在五种分类中切换，观察类的数量与关系矩阵如何对应。然后展开证明，解释为什么不同等价类不可能交叠。',source:'教材 §1.1 · 定义 1.1.4 · 定理 1.1.1<br>第 4—5 页',label:'分类 ⇄ 等价关系',render:renderPartition},
    {id:'powers',nav:'方幂与指数',title:'先定义重复，<br>再理解指数法则。',lead:'正整数幂表示重复相乘；零次幂规定为单位元；负整数幂通过逆元定义。加群中相应地使用倍数记号。',formula:'a⁰ = e，a⁻ⁿ = (a⁻¹)ⁿ<br>aᵐaⁿ = aᵐ⁺ⁿ',definition:'对任意整数 m、n，还成立 (aᵐ)ⁿ = aᵐⁿ。对不同元素，(ab)ⁿ = aⁿbⁿ 不能随意使用；ab = ba 时才可保证。',prompt:'把 m 或 n 调成负数，观察逆元如何抵消。比较两边结果，并区分乘法记号和加法记号。',source:'教材 §1.2 · 方幂与指数法则<br>第 14—15 页',label:'整数指数 · 在具体群中计算',render:renderPowers},
    {id:'criteria',nav:'群的判别',title:'换一种条件，<br>仍能认出群。',lead:'在非空集合上给定代数运算后，除了直接验证群公理，还可以用同侧单位元与逆元，或群方程的可解性来判别。',formula:'结合律 + 方程总有解<br>⇔ 群',definition:'这里的方程是：对所有 a、b，ax = b 与 ya = b 都有解。有限集合上，结合律与两侧消去律也足以判别。',prompt:'依次查看三种判别方式。特别检查“有限”条件：正整数加法满足结合律与消去律，为什么仍不是群？',source:'教材 §1.2 · 定理 1.2.3—1.2.4 · 例 11<br>第 15—17 页',label:'从判别条件到群公理',render:renderCriteria}
  );
  const requestedBook=new URLSearchParams(location.search).get('section');
  const legacyAnchor=location.hash.slice(1)==='order'?'powers':location.hash.slice(1);
  const bookId=Object.hasOwn(textbookSections,requestedBook)?requestedBook:(textbookSections['1.2'].items.filter(id=>id!=='check').includes(legacyAnchor)?'1.2':'1.1');
  const book=textbookSections[bookId];
  const sections=book.items.map(id=>({...allSections.find(s=>s.id===id),kicker:`§ ${bookId} · ${book.title}`}));
  Object.assign(sections.find(s=>s.id==='check'),{nav:'教材习题',title:'这一节的概念，<br>能说清楚了吗？',lead:'从本节课后习题出发，通过具体变式检查概念，再逐步展开证明，最后回到教材原题。',definition:bookId==='1.1'?'能辨认等价关系、说明等价类，并解释等价关系与分类的对应。':'能验证群公理、使用基本性质、计算整数幂，并说明判别定理的条件。',source:`教材 §${bookId} · ${book.homework}`,label:`§${bookId} · 概念检查`});
  $('intro-kicker').textContent=`第一讲 / § ${bookId}`;
  $('intro-title').textContent=book.title;
  $('intro-line').textContent=book.line;
  $('intro-path').textContent=book.path;
  $('reference-reading').textContent=`《近世代数》第三版 · §${bookId} ${book.title}，第 ${book.pages} 页。${book.homework}。`;
  document.title=`§${bookId} ${book.title} · 第一讲 | 抽象代数 I`;
  document.querySelectorAll('[data-textbook-section]').forEach(a=>a.setAttribute('aria-current',a.dataset.textbookSection===bookId?'page':'false'));
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
    $('page-count').textContent=`${current+1} / ${sections.length}`;
    const url=new URL(location.href);url.searchParams.set('section',bookId);url.hash=s.id;
    history.replaceState(null,'',url);scene.dataset.lessonScene=s.id;window.dispatchEvent(new Event('lesson-topic'));scene.innerHTML='';s.render();window.dispatchEvent(new Event('lesson-rendered'));
    if(focus)$('workspace').focus({preventScroll:true});
  }
  $('chapter-nav').addEventListener('click',e=>{const b=e.target.closest('button');if(b)show(Number(b.dataset.section));});
  $('previous').onclick=()=>show(current-1);$('next').onclick=()=>show(current+1);
  document.addEventListener('keydown',e=>{if(e.altKey||e.ctrlKey||e.metaKey||e.shiftKey||e.target.closest('input,select,textarea,button,summary,[contenteditable]'))return;if(e.key==='ArrowRight'||e.key==='ArrowLeft'){e.preventDefault();const delta=e.key==='ArrowRight'?1:-1;if(window.LessonScreen)window.LessonScreen.step(delta);else show(current+delta,{focus:true});}});
  window.addEventListener('hashchange',()=>{const n=sections.findIndex(s=>s.id===location.hash.slice(1));if(n>=0&&n!==current)show(n);});
  window.addEventListener('resize',()=>onResize());
  // Teaching layout is useful even where native fullscreen is unavailable.
  let ownsNativeFullscreen=false;
  const mobileReading=matchMedia('(max-width: 767px), (pointer: coarse) and (max-width: 1024px)');
  function setPresentation(active){
    document.body.classList.toggle('present',active);
    $('fullscreen').setAttribute('aria-pressed',String(active));
    $('fullscreen').textContent=active?'退出授课 ↙':'全屏讲授 ↗';
    requestAnimationFrame(()=>onResize());
  }
  function exitNativeFullscreen(){
    try{document.exitFullscreen?.()?.catch?.(()=>{});}catch{}
  }
  $('fullscreen').setAttribute('aria-pressed','false');
  function syncPresentationAvailability(){
    $('fullscreen').hidden=mobileReading.matches;
    $('fullscreen').disabled=mobileReading.matches;
    if(mobileReading.matches){
      setPresentation(false);
      if(ownsNativeFullscreen&&document.fullscreenElement===document.documentElement)exitNativeFullscreen();
      ownsNativeFullscreen=false;
    }
  }
  mobileReading.addEventListener('change',syncPresentationAvailability);
  syncPresentationAvailability();
  $('fullscreen').onclick=()=>{
    if(mobileReading.matches)return;
    const active=!document.body.classList.contains('present');
    setPresentation(active);
    if(!active){ownsNativeFullscreen=false;if(document.fullscreenElement===document.documentElement)exitNativeFullscreen();return;}
    if(document.fullscreenEnabled===false)return;
    try{document.documentElement.requestFullscreen?.()?.catch?.(()=>{});}catch{}
  };
  document.addEventListener('fullscreenchange',()=>{
    if(document.fullscreenElement===document.documentElement){
      if(!mobileReading.matches&&document.body.classList.contains('present'))ownsNativeFullscreen=true;
      else exitNativeFullscreen();
    }else if(ownsNativeFullscreen){ownsNativeFullscreen=false;setPresentation(false);}
  });
  document.addEventListener('keydown',event=>{
    if(event.key==='Escape'&&!document.fullscreenElement&&document.body.classList.contains('present')&&!document.querySelector('dialog[open]')){
      event.preventDefault();setPresentation(false);
    }
  });

  function renderRelation(){
    let R=M.fromBlocks([[0,1],[2]]);const letters=['a','b','c'];
    scene.innerHTML=`<div class="controls"><label>观察例子 <select id="relation-preset"><option value="equivalence">一个等价关系</option><option value="reflexive">只缺反身性</option><option value="symmetric">只缺对称性</option><option value="transitive">只缺传递性</option><option value="custom" disabled>自定义关系</option></select></label><span class="spacer"></span><button type="button" id="repair">补成等价关系</button></div><div class="relation-layout"><div id="relation-graph" class="stage"></div><div id="relation-matrix"></div></div><p class="hint">点击矩阵方格：● 表示行元素与列元素有关系，· 表示没有。箭头有方向，自环表示与自己相关。</p><div id="relation-properties" class="property-row"></div><p class="section-small">三个元素的全部五种分类 / 点击查看对应关系</p><div id="partition-options" class="partition-options"></div><div id="status" class="status-strip" role="status" aria-live="polite"></div><details class="mini-proof"><summary>把图形翻译成定义与证明</summary><p class="theorem-statement">等价类的基本结论：设 ∼ 是非空集合 S 上的等价关系，则每个 [a] 非空，所有类覆盖 S，且任意两类要么相等、要么不相交。因此全部不同的等价类构成 S 的一个分类。</p><p>对任意 a, b, c ∈ S：<br>反身性：a ∼ a。<br>对称性：a ∼ b ⇒ b ∼ a。<br>传递性：a ∼ b 且 b ∼ c ⇒ a ∼ c。</p><p><b>从等价关系到分类：</b>若 c ∈ [a] ∩ [b]，对任意 x ∈ [a]，有 x ∼ a、a ∼ c、c ∼ b，由传递性得 x ∼ b，所以 [a] ⊆ [b]。反向同理。因此 [a] = [b]。反身性保证每个元素都在自己的类中；不同的类于是非空、不重、不漏。</p><p><b>从分类到等价关系：</b>规定“两元素在同一类”就是等价。每个元素在自己的类中；同一类的归属是对称的；如果 a、b 同类，b、c 同类，因为 b 只属于一个类，a、c 也同类。三条性质因此都成立。</p></details>`;
    function update(message){
      const result=M.inspectRelation(R);const f=result.failures;
      const P=[[85,172],[210,65],[335,172]];let content=`<defs><marker id="arrow-r" markerWidth="6" markerHeight="6" refX="5" refY="3" orient="auto-start-reverse"><path d="M0 0L6 3L0 6" fill="none" stroke="var(--diagram-edge,#668d7e)"/></marker></defs>`;
      for(let a=0;a<3;a++)for(let b=0;b<3;b++)if(R[a][b]){
        const [x,y]=P[a],[u,v]=P[b];
        if(a===b)content+=`<path d="M ${x-16} ${y-21} C ${x-57} ${y-76}, ${x+57} ${y-76}, ${x+16} ${y-21}" fill="none" stroke="var(--diagram-edge,#668d7e)" stroke-width="1.5" marker-end="url(#arrow-r)"/>`;
        else{const dx=u-x,dy=v-y,len=Math.hypot(dx,dy),ox=-dy/len*15,oy=dx/len*15;content+=`<path d="M${x+dx/len*29} ${y+dy/len*29} Q ${(x+u)/2+ox} ${(y+v)/2+oy} ${u-dx/len*32} ${v-dy/len*32}" fill="none" stroke="var(--diagram-edge,#668d7e)" stroke-width="1.6" marker-end="url(#arrow-r)"/>`;}
      }
      P.forEach(([x,y],a)=>{const c=result.valid?result.blocks.findIndex(b=>b.includes(a)):a;content+=`<circle cx="${x}" cy="${y}" r="28" fill="${soft[c]}" stroke="${colors[c]}" stroke-width="1.5"/><text x="${x}" y="${y+7}" text-anchor="middle" class="math-label" font-size="24" fill="${colors[c]}">${letters[a]}</text>`;});
      $('relation-graph').innerHTML=svg(content,'0 0 420 245',result.valid?'有向关系图：同色节点属于同一等价类':'有向关系图：当前关系不满足全部等价关系性质');
      $('relation-matrix').innerHTML=`<table class="matrix"><caption>行 → 列</caption><thead><tr><th></th>${letters.map(x=>`<th scope="col">${x}</th>`).join('')}</tr></thead><tbody>${R.map((row,a)=>`<tr><th scope="row">${letters[a]}</th>${row.map((v,b)=>`<td><button type="button" data-a="${a}" data-b="${b}" class="${v?'on':''}" aria-pressed="${v}" aria-label="${letters[a]} 与 ${letters[b]} ${v?'有':'没有'}关系，点击切换">${v?'●':'·'}</button></td>`).join('')}</tr>`).join('')}</tbody></table>`;
      const explanations=[f.reflexive?`${letters[f.reflexive[0]]} 与自身无关系`:'每个元素都有自环',f.symmetric?`${letters[f.symmetric[0]]} → ${letters[f.symmetric[1]]} 缺少反向`:'每条箭头都有反向',f.transitive?`${f.transitive.map(a=>letters[a]).join(' → ')} 缺少捷径`:'两步可达也能直接到达'];
      $('relation-properties').innerHTML=['反身性','对称性','传递性'].map((x,i)=>`<div class="property ${Object.values(f)[i]?'fail':''}"><b>${x}</b><em class="property-mark" aria-hidden="true">${Object.values(f)[i]?'✕':'✓'}</em><span>${explanations[i]}</span><span class="sr-only">${Object.values(f)[i]?'不成立':'成立'}</span></div>`).join('');
      $('partition-options').innerHTML=M.partitions3.map((p,i)=>`<button type="button" data-partition="${i}" aria-pressed="${JSON.stringify(M.fromBlocks(p))===JSON.stringify(R)}">${p.map(b=>`{${b.map(a=>letters[a]).join(',')}}`).join(' | ')}</button>`).join('');
      setStatus((message?message+'<br>':'')+(result.valid?`<strong>形成分类。</strong> S / ∼ = { ${result.blocks.map(b=>`{${b.map(a=>letters[a]).join(', ')}}`).join(', ')} }`:'<strong>还不能作为等价关系。</strong> 找到一个反例，就足以否定对应性质。'),!result.valid);
    }
    $('relation-matrix').onclick=e=>{const b=e.target.closest('button');if(!b)return;const a=+b.dataset.a,c=+b.dataset.b;R[a][c]=!R[a][c];$('relation-preset').value='custom';update();$('relation-matrix').querySelector(`[data-a="${a}"][data-b="${c}"]`).focus({preventScroll:true});};
    $('partition-options').onclick=e=>{const b=e.target.closest('button');if(b){R=M.fromBlocks(M.partitions3[+b.dataset.partition]);$('relation-preset').value='equivalence';update();}};
    $('relation-preset').onchange=e=>{R=e.target.value==='reflexive'?[[true,true,false],[true,true,false],[false,false,false]]:e.target.value==='symmetric'?[[true,true,true],[false,true,true],[false,false,true]]:e.target.value==='transitive'?[[true,true,false],[true,true,true],[false,true,true]]:M.fromBlocks([[0,1],[2]]);update();};
    $('repair').onclick=()=>{let before=R.flat().filter(Boolean).length;for(let a=0;a<3;a++){R[a][a]=true;for(let b=0;b<3;b++)R[a][b]=R[b][a]=R[a][b]||R[b][a];}for(let k=0;k<3;k++)for(let a=0;a<3;a++)for(let b=0;b<3;b++)R[a][b]=R[a][b]||(R[a][k]&&R[k][b]);update(`补入 ${R.flat().filter(Boolean).length-before} 个有序对，得到包含原关系的最小等价关系。`);};
    update();
  }

  function renderPartition(){
    let chosen=1;
    const letters=['a','b','c'];
    scene.innerHTML=`<p class="hint">集合 S = {a, b, c} 的全部五种分类</p><div id="partition-tabs" class="controls"></div><div id="partition-blocks" class="partition-blocks"></div><p class="partition-arrow">同一类 ⇄ 彼此等价</p><div id="partition-relation" class="insight" aria-live="polite"></div><details class="mini-proof"><summary>定理 1.1.1：等价关系与分类的对应</summary><p class="theorem-statement">设 S 为非空集合。S 上的每个等价关系都给出一个由全部等价类组成的分类；反之，每个分类都确定一个等价关系：两元素等价当且仅当它们属于同一类。这两个构造互为逆过程。</p><h3>证明</h3><p><b>等价关系 → 分类：</b>由反身性，a ∈ [a]，因此每个等价类非空，所有类覆盖 S。若 [a] 与 [b] 相交，取公共元素 c，由对称性与传递性得 a ∼ b，进而 [a] = [b]。所以不同等价类互不相交。</p><p><b>分类 → 等价关系：</b>规定 a ∼ b 当且仅当 a、b 在同一类。每个元素与自己同类；同类关系对称；若 a、b 同类且 b、c 同类，因为 b 只属于一类，a、c 也同类。因此三条性质都成立。</p></details>`;
    function draw(){
      const blocks=M.partitions3[chosen];
      $('partition-tabs').innerHTML=M.partitions3.map((p,i)=>`<button type="button" data-part="${i}" aria-pressed="${i===chosen}">${p.map(b=>`{${b.map(a=>letters[a]).join(',')}}`).join(' | ')}</button>`).join('');
      $('partition-blocks').innerHTML=blocks.map((b,i)=>`<div class="partition-block" style="--block-color:${colors[i]};--block-soft:${soft[i]}"><div>${b.map(a=>`<span>${letters[a]}</span>`).join('')}</div><p>{${b.map(a=>letters[a]).join(', ')}}</p></div>`).join('');
      const pairs=M.fromBlocks(blocks).flatMap((row,a)=>row.flatMap((yes,b)=>yes?[`(${letters[a]}, ${letters[b]})`]:[]));
      $('partition-relation').innerHTML=`<p>对应的关系，由这些有序对组成：</p><div class="pair-list">${pairs.map(pair=>`<span>${pair}</span>`).join('')}</div><p>商集 S / ∼ 有 <b>${blocks.length}</b> 个元素，每个元素就是上方的一整个类。</p>`;
    }
    $('partition-tabs').onclick=e=>{const b=e.target.closest('button');if(b){chosen=+b.dataset.part;draw();}};
    draw();
  }

  function renderPowers(){
    let key='unit5',a=2,m=2,n=-1;
    scene.innerHTML=`<div class="order-controls"><label>选择群<select id="powers-group"><option value="unit5">U(5) · 乘法</option><option value="add6">ℤ₆ · 加法</option><option value="d3">D₃ · 变换复合</option></select></label><label>固定元素 a<select id="powers-element"></select></label></div><div class="control-pair"><label>整数 m <output id="powers-m-value"></output><input id="powers-m" type="range" min="-4" max="4" value="2"></label><label>整数 n <output id="powers-n-value"></output><input id="powers-n" type="range" min="-4" max="4" value="-1"></label></div><div id="power-rules" class="power-rules" aria-live="polite"></div><div id="power-track" class="power-track"></div><div id="status" class="status-strip" role="status" aria-live="polite"></div><details class="mini-proof"><summary>为什么不能随意拆开 (ab)ⁿ？</summary><p>(ab)² = abab，而 a²b² = aabb。要把中间的 b、a 换位，需要 ab = ba。结合律只允许移动括号。</p><p>在 D₃ 中取 a = r、b = s，则 (rs)² = e，但 r²s² = r²，二者不同。</p></details>`;
    function elements(){const model=M.model(key);if(!model.elements.includes(a))a=model.elements[1];$('powers-element').innerHTML=model.elements.map(x=>`<option value="${x}" ${x===a?'selected':''}>${model.label(x)}</option>`).join('');}
    function draw(){
      const model=M.model(key),e=model.identity,inv=model.elements.find(b=>model.op(a,b)===e&&model.op(b,a)===e),add=key==='add6';
      const power=(x,k)=>{const factor=k<0?model.elements.find(b=>model.op(x,b)===e&&model.op(b,x)===e):x;let v=e;for(let j=0;j<Math.abs(k);j++)v=model.op(v,factor);return v;};
      const fmt=model.label,expression=k=>add?`${k} · ${fmt(a)}`:`(${fmt(a)})<sup>${k}</sup>`;
      const left=model.op(power(a,m),power(a,n)),right=power(a,m+n),nested=power(power(a,m),n);
      $('powers-m-value').textContent=m;$('powers-n-value').textContent=n;
      $('power-rules').innerHTML=`<article><p>${add?'倍数相加':'同底数幂相乘'}</p><div class="formula">${expression(m)} ${model.opSymbol} ${expression(n)} = ${expression(m+n)}</div><strong>${fmt(left)} = ${fmt(right)}</strong></article><article><p>${add?'倍数的倍数':'幂的幂'}</p><div class="formula">${add?`${n} · (${expression(m)})`:`(${expression(m)})<sup>${n}</sup>`} = ${expression(m*n)}</div><strong>${fmt(nested)} = ${fmt(power(a,m*n))}</strong></article>`;
      const factor=m<0?inv:a,steps=[e];for(let j=0;j<Math.abs(m);j++)steps.push(model.op(steps[steps.length-1],factor));
      $('power-track').innerHTML=`<p>计算 ${expression(m)}：${m===0?'从单位元开始，运算 0 次':`每次${add?'加':'乘'} ${fmt(factor)}${m<0?'（a 的逆元）':''}`}</p><div class="power-steps">${steps.map((v,i)=>`${i?'<i aria-hidden="true">→</i>':''}<span>${fmt(v)}</span>`).join('')}</div>`;
      setStatus(add?`加法记号下：0 · ${fmt(a)} = [0]，负倍数通过负元 ${fmt(inv)} 计算。`:`零次幂等于单位元 ${fmt(e)}；${fmt(a)} 的逆元是 ${fmt(inv)}，所以负指数表示重复乘这个逆元。`);
    }
    $('powers-group').onchange=e=>{key=e.target.value;a=key==='d3'?1:2;elements();draw();};$('powers-element').onchange=e=>{a=+e.target.value;draw();};
    $('powers-m').oninput=e=>{m=+e.target.value;draw();};$('powers-n').oninput=e=>{n=+e.target.value;draw();};elements();draw();
  }

  function renderCriteria(){
    const criteria=[
      {name:'同侧单位元与逆元',ref:'定理 1.2.3',condition:'非空集合 + 代数运算 + 结合律 + 左单位元 + 每个元素的左逆元',steps:['设 ea = a，且每个 a 都有 a′，使 a′a = e。','a′ 也有左逆元 a″，所以 a″a′ = e。','aa′ = e(aa′) = (a″a′)(aa′) = a″(a′a)a′ = a″(ea′) = a″a′ = e。','ae = a(a′a) = (aa′)a = ea = a。因此左单位元与左逆元也是右侧的。'],note:'“每个元素都有左逆元”必须对 a′ 也成立；这正是证明中引入 a″ 的依据。'},
      {name:'群方程总有解',ref:'定理 1.2.4',condition:'非空集合 + 代数运算 + 结合律 + 对所有 a、b，ax = b 与 ya = b 都有解',steps:['固定 b。由 yb = b 有解，取 e 使 eb = b。','对任意 a，由 bx = a 有解，可写 a = bc。','ea = e(bc) = (eb)c = bc = a，因此 e 是全体元素的左单位元。','由 ya = e 有解，每个 a 都有左逆元。应用定理 1.2.3，得到群。'],note:'已知“对每一对 a、b 都可解”，才能固定 b 后覆盖所有 a；只解一个方程不够。'},
      {name:'有限集合的消去律',ref:'例 11',condition:'非空有限集合 + 代数运算 + 结合律 + 左、右消去律',steps:['设 G = {a₁, …, aₙ}。固定 a，考察 aa₁, …, aaₙ。','由左消去律，这 n 个结果两两不同。','它们都属于只有 n 个元素的 G，所以遍历 G；于是 ax = b 对每个 b 都可解。','右消去律同样保证 ya = b 可解。再用定理 1.2.4，得到群。'],note:'有限条件不可删去：(ℕ₊, +) 满足结合律与两侧消去律，却没有单位元 0，因此不是群。'}
    ];
    const statements=[
      '<p>设 G 为非空集合，已给定代数运算。以下条件成立，当且仅当 G 是群：</p><ol><li>运算满足结合律。</li><li>存在 e ∈ G，对每个 a ∈ G，都有 ea = a。</li><li>对每个 a ∈ G，存在 a′ ∈ G，使 a′a = e。</li></ol><p class="theorem-note">其中 e 是同一个左单位元，a′ 是相对于 e 的左逆元。</p>',
      '<p>设 G 为非空集合，已给定满足结合律的代数运算。</p><p>G 是群，当且仅当对任意 a、b ∈ G，以下两个方程在 G 中都有解：</p><ol><li>ax = b</li><li>ya = b</li></ol><p class="theorem-note">x、y 是待求元素。这里只要求解存在，不预先要求唯一。</p>',
      '<p>设 G 为非空有限集合，已给定代数运算。若以下条件成立，则 G 是群：</p><ol><li>运算满足结合律。</li><li>左消去律：对任意 a、b、c ∈ G，ab = ac ⇒ b = c。</li><li>右消去律：对任意 a、b、c ∈ G，ba = ca ⇒ b = c。</li></ol><p class="theorem-note">这里的有限性、非空性、结合律及左右消去律都是假设。</p>'
    ];
    criteria.push({"name": "扩展：右单位元", "ref": "定理 1.2.4 · 扩展 A", "condition": "结合律；∃a₀ ∃e [a₀e = a₀ 且 ∀b ∃y (ya₀ = b)]", "steps": ["按假设固定 a₀ ∈ S，并选定 e ∈ S，使 a₀e = a₀。此后 e 不随 b 改变。", "任取 b ∈ S。由对同一个 a₀ 的可解性，存在 y ∈ S，使 ya₀ = b。", "be = (ya₀)e = y(a₀e) = ya₀ = b。中间一步仅使用结合律。", "由于 b 任意，同一个 e 满足对所有 b ∈ S 有 be = b，故 e 是右单位元。这里不需要消去律、有限性或解的唯一性。", "不能推出群：取 S = {0,1}，定义 uv = u。则 (uv)w = u = u(vw)，故结合律成立。任取固定 a₀，a₀e = a₀ 对每个 e 成立；对任意 b，取 y = b 即有 ya₀ = b。", "若 f 是左单位元，则 f0 = 0、f1 = 1；但该运算给出 f0 = f1 = f，矛盾。因此没有左单位元，更不是群。每个元素却都是右单位元，故右单位元也未必唯一。"], "note": "两项条件中的 a₀ 是同一个固定元素；先选 a₀ 与 e，再任取 b。所有解都要求属于 S。"},{"name": "扩展：左单位元（对偶）", "ref": "定理 1.2.4 · 扩展 B（对偶）", "condition": "结合律；∃a₀ ∃e [ea₀ = a₀ 且 ∀b ∃x (a₀x = b)]", "steps": ["按对偶假设固定 a₀ ∈ S，并选定 e ∈ S，使 ea₀ = a₀。此后 e 不随 b 改变。", "任取 b ∈ S。存在 x ∈ S，使 a₀x = b。这里仍使用同一个固定元素 a₀。", "eb = e(a₀x) = (ea₀)x = a₀x = b。因此 e 是全体元素的左单位元。", "对偶的含义：在 S 上定义反向乘法 u ⋆ v = vu。由 (u ⋆ v) ⋆ w = w(vu) = (wv)u = u ⋆ (v ⋆ w)，⋆ 也满足结合律。对 ⋆ 应用扩展 A，所得右单位元正是原乘法的左单位元。", "对偶反例：取 S = {0,1}，定义 uv = v。则 (uv)w = w = u(vw)。任取固定 a₀，ea₀ = a₀ 对每个 e 成立；对任意 b，取 x = b 即有 a₀x = b。", "若 f 是右单位元，则 0f = 0、1f = 1；但该运算给出 0f = 1f = f，矛盾。因此没有右单位元，也不是群。每个元素都是左单位元，故左单位元也未必唯一。"], "note": "两项条件中的 a₀ 是同一个固定元素；先选 a₀ 与 e，再任取 b。所有解都要求属于 S。"});
    statements.push("<p>设 S 为非空集合，具有满足结合律的二元运算 S × S → S。</p><p>若存在固定 a₀ ∈ S，使 a₀x = a₀ 在 S 中有解，且对每个 b ∈ S，ya₀ = b 在 S 中有解，则 a₀x = a₀ 的每个解都是 S 的右单位元。</p><p class=\"theorem-note\">两项条件中的 a₀ 是同一个固定元素；先选 a₀ 与 e，再任取 b。所有解都要求属于 S。</p><p>结论只保证单侧单位元存在，不保证另一侧、唯一性或群结构。</p>","<p>设 S 为非空集合，具有满足结合律的二元运算 S × S → S。</p><p>若存在固定 a₀ ∈ S，使 ya₀ = a₀ 在 S 中有解，且对每个 b ∈ S，a₀x = b 在 S 中有解，则 ya₀ = a₀ 的每个解都是 S 的左单位元。</p><p class=\"theorem-note\">两项条件中的 a₀ 是同一个固定元素；先选 a₀ 与 e，再任取 b。所有解都要求属于 S。</p><p>结论只保证单侧单位元存在，不保证另一侧、唯一性或群结构。</p>");
    criteria[3].counterexample={rule:'uv = u',rows:[[0,0],[1,1]]};
    criteria[4].counterexample={rule:'uv = v',rows:[[0,1],[0,1]]};
    function counterexampleTable(c){
      if(!c.counterexample||step<4)return '';
      const {rule,rows}=c.counterexample;
      return `<figure class="identity-counterexample"><table><caption><span>反例乘法表</span> · ${rule}</caption><thead><tr><th scope="col">·</th><th scope="col">0</th><th scope="col">1</th></tr></thead><tbody>${rows.map((row,i)=>`<tr><th scope="row">${i}</th>${row.map(value=>`<td>${value}</td>`).join('')}</tr>`).join('')}</tbody></table><figcaption>行是左因子，列是右因子；表内为乘积。</figcaption></figure>`;
    }
    criteria[0].steps.unshift('必要性：若 G 已是群，结合律、左单位元和左逆元都由群的定义成立。充分性：下面证明给定的 e、a′ 同时也满足右侧条件。');
    criteria[1].steps.unshift('必要性：若 G 是群，x = a⁻¹b、y = ba⁻¹ 给出所需解。充分性：下面只用结合律和两类方程的可解性来构造单位元与逆元。');
    let chosen=0,step=-1;
    scene.innerHTML=`<div id="criteria-tabs" class="controls proof-options"></div><p id="criteria-condition" class="insight"></p><div id="criteria-proof" class="proof-board stage" aria-live="polite"></div><div class="controls"><button id="criteria-back" type="button">← 上一步</button><button id="criteria-next" class="primary" type="button">下一步 →</button><span id="criteria-count" class="hint"></span></div><p id="criteria-note" class="status-strip"></p>`;
    function draw(){const c=criteria[chosen];$('criteria-tabs').innerHTML=criteria.map((x,i)=>`<button type="button" data-criterion="${i}" aria-pressed="${chosen===i}">${x.name}</button>`).join('');$('criteria-condition').textContent=step<0?'':c.condition;$('criteria-condition').hidden=step<0;$('criteria-proof').innerHTML=`<p class="label"><span>${c.ref}</span> · <span>${step<0?'定理阐述':'证明'}</span></p>${step<0?`<div class="theorem-statement">${statements[chosen]}</div>`:`${counterexampleTable(c)}<p class="criteria-step">${c.steps[step]}</p>`}`;$('criteria-back').disabled=step<0;$('criteria-back').textContent=step===0?'← 返回定理':'← 上一步';$('criteria-next').textContent=step<0?'开始证明 →':'下一步 →';$('criteria-next').disabled=step===c.steps.length-1;$('criteria-count').textContent=step<0?'先读清条件与结论':`${step+1} / ${c.steps.length}`;$('criteria-note').textContent=c.note;$('criteria-note').hidden=step<0;}
    $('criteria-tabs').onclick=e=>{const b=e.target.closest('button');if(b){chosen=+b.dataset.criterion;step=-1;draw();}};$('criteria-back').onclick=()=>{step--;draw();};$('criteria-next').onclick=()=>{step++;draw();};draw();
  }

  function renderQuotient(){
    let m=3,t=0,a=1;
    scene.innerHTML=`<div class="controls"><label>模数 m <select id="modulus">${M.range(5).map(i=>`<option value="${i+2}" ${i===1?'selected':''}>${i+2}</option>`).join('')}</select></label><span class="spacer"></span><button id="quotient-play" type="button" class="primary">看一次分类 →</button></div><div id="quotient-graph" class="stage quotient-stage"></div><div class="control-pair"><label>观察尺度 <output id="scale-label">整数</output><input id="quotient-scale" type="range" min="0" max="100" value="0" aria-label="观察尺度：整数到分类到商集"></label><label>代表元 a <output id="representative-value">1</output><input id="representative" type="range" min="-6" max="11" value="1" aria-label="选择代表元"></label></div><div id="quotient-class" class="insight"></div><div id="status" class="status-strip" role="status" aria-live="polite"></div><p class="hint">图示窗口 −6 ≤ a ≤ 11。每一类还向两端无限延伸；压成的点代表整个集合，不代表某个整数。</p>`;
    function draw(){
      const compact=scene.clientWidth<620,W=compact?400:760;
      const values=M.range(18).map(i=>i-6),r=M.mod(a,m),group=Math.min(1,t*2),collapse=Math.max(0,t*2-1);const cx=i=>(compact?40:70)+i*(compact?320:620)/(m-1);let content='';
      for(let i=0;i<m;i++){
        const count=values.filter(v=>M.mod(v,m)===i).length;
        content+=`<rect x="${cx(i)-38}" y="${180-(count*34+40)/2}" width="76" height="${count*34+40}" rx="36" fill="${soft[i]}" opacity="${group*(1-collapse)}"/><text x="${cx(i)}" y="374" text-anchor="middle" font-size="22" fill="${colors[i]}" opacity="${group}">[${i}]</text>`;
      }
      values.forEach((v,i)=>{
        const cl=M.mod(v,m),members=values.filter(w=>M.mod(w,m)===cl),idx=members.indexOf(v);const x0=(compact?30:65)+(i%6)*(compact?68:126),y0=65+Math.floor(i/6)*108;const gx=cx(cl),gy=180+(idx-(members.length-1)/2)*34;const x=x0+(gx-x0)*group,y=(y0+(gy-y0)*group)*(1-collapse)+180*collapse;
        content+=`<g class="group-point" data-integer="${v}" tabindex="0" role="button" aria-label="选择代表元 ${v}，属于 [${cl}] 类" opacity="${1-collapse*.75}"><circle cx="${x}" cy="${y}" r="${v===a?23:20}" fill="${v===a?colors[cl]:soft[cl]}" stroke="${colors[cl]}" stroke-width="${v===a?2:1}"/><text x="${x}" y="${y+5}" font-size="${compact?24:21}" text-anchor="middle" fill="${v===a?'var(--diagram-solid-text,#fff)':colors[cl]}" opacity="${1-collapse}">${v}</text></g>`;
      });
      if(collapse>0)for(let i=0;i<m;i++)content+=`<g pointer-events="none" opacity="${collapse}"><circle cx="${cx(i)}" cy="180" r="${i===r?32:26}" fill="${soft[i]}" stroke="${colors[i]}" stroke-width="${i===r?3:1.5}"/><text x="${cx(i)}" y="188" font-size="27" class="math-label" text-anchor="middle" fill="${colors[i]}">[${i}]</text></g>`;
      $('quotient-graph').innerHTML=svg(content,`0 0 ${W} 390`,`模 ${m} 的分类。代表元 ${a} 属于剩余类 [${r}]；商集共有 ${m} 个元素。`);
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
      $('rep-result').innerHTML=`<div class="formula">${a<0?'('+a+')':a} ${op} ${b<0?'('+b+')':b} = ${res} <span style="color:var(--diagram-ghost,#9ca997)">↦</span> <strong style="color:var(--pine)">[${M.mod(res,m)}]</strong></div><p>[2] ${op} [4] = [${canonical}] = [${M.mod(canonical,m)}]，与 k、ℓ 的取值无关。</p>`;
      $('operation-proof').innerHTML=multiply?'<b>一般的理由</b><br>若 a′ = a + 5k，b′ = b + 5ℓ，则<br><span class="formula">a′b′ − ab = 5(kb + ℓa + 5kℓ)</span><br>差仍是 5 的倍数，所以乘积在同一类中。':'<b>一般的理由</b><br>若 a′ = a + 5k，b′ = b + 5ℓ，则<br><span class="formula">(a′ + b′) − (a + b) = 5(k + ℓ)</span><br>差是 5 的倍数，所以和在同一类中。';
      setStatus(`这次计算与标准代表的结果相差 ${res-canonical} = 5 × (${(res-canonical)/m})。<strong>变的是代表，不变的是结果所属的类。</strong>`);
    }
    $('rep-k').oninput=e=>{k=+e.target.value;draw();};$('rep-l').oninput=e=>{l=+e.target.value;draw();};$('operation-kind').onchange=e=>{multiply=e.target.value==='multiply';draw();};draw();
  }

  function renderSymmetry(){
    let A=1,B=3,busy=false,displayedLeft,displayedRight;
    const names=['e · 不动','r · 旋转 120°','r² · 旋转 240°','s · 竖轴反射','rs · 先 s 后 r','r²s · 先 s 后 r²'];
    scene.innerHTML=`<div class="two-selects"><label>操作 A<select id="sym-a">${names.map((n,i)=>`<option value="${i}" ${i===A?'selected':''}>${n}</option>`).join('')}</select></label><label>操作 B<select id="sym-b">${names.map((n,i)=>`<option value="${i}" ${i===B?'selected':''}>${n}</option>`).join('')}</select></label></div><div id="symmetry-graph" class="stage symmetry-stage"></div><div id="sym-readout" class="action-readout"></div><div class="controls"><button type="button" id="sym-play" class="primary">同时播放两种顺序</button><span id="sym-step" class="hint" role="status" aria-live="polite"></span></div><div class="symmetry-legend"><span>虚线：初始位置</span><span>1 / 2 / 3：跟踪顶点</span><span>复合记号统一先右后左</span></div><div id="status" class="status-strip" role="status" aria-live="polite"></div><details class="mini-proof"><summary>为什么这六个变换构成群？</summary><p>任意两个三角形的对称复合后，仍是三角形的对称；函数复合满足结合律；e 什么也不改变；旋转和反射都可以撤销，所以每个变换都有逆元。这些正是前一主题中群定义的各项要求。过渡帧用于展示运动，只有每一步的端点表示列出的六个群元素。</p></details>`;
    const base=M.range(3).map(i=>[-92*Math.sin(i*2*Math.PI/3),-92*Math.cos(i*2*Math.PI/3)]);
    const positions=g=>M.range(3).map(i=>base[M.d3apply(g,i)]);
    function triangle(points,cx){const cy=133;let s=`<path d="${base.map(([x,y],i)=>`${i?'L':'M'}${x+cx},${y+cy}`).join('')}Z" fill="none" stroke="var(--diagram-line,#b9c9bd)" stroke-dasharray="5 6" stroke-width="1.3"/><path d="${points.map(([x,y],i)=>`${i?'L':'M'}${x+cx},${y+cy}`).join('')}Z" fill="var(--diagram-wash,#dcebe255)" stroke="var(--diagram-edge,#547f6d)" stroke-width="1.6"/>`;
      points.forEach(([x,y],i)=>{s+=`<circle cx="${cx+x}" cy="${cy+y}" r="19" fill="${colors[i]}"/><text x="${cx+x}" y="${cy+y+6}" text-anchor="middle" font-size="24" fill="var(--diagram-solid-text,#fff)">${i+1}</text>`;});return s;}
    function draw(left=positions(M.d3mul(B,A)),right=positions(M.d3mul(A,B))){
      displayedLeft=left;displayedRight=right;
      const stacked=scene.clientWidth<580;
      const second=stacked?`<g transform="translate(0 290)">${triangle(right,160)}<text x="160" y="261" text-anchor="middle" font-size="24" fill="var(--diagram-muted,#61736c)">先 B，后 A</text></g>`:`${triangle(right,480)}<text x="480" y="261" text-anchor="middle" font-size="24" fill="var(--diagram-muted,#61736c)">先 B，后 A</text>`;
      $('symmetry-graph').innerHTML=svg(`${stacked?'':'<path d="M320 35V240" stroke="var(--diagram-line,#e1e6dc)"/>'}${triangle(left,160)}<text x="160" y="261" text-anchor="middle" font-size="24" fill="var(--diagram-muted,#61736c)">先 A，后 B</text>${second}`,stacked?'0 0 320 575':'0 0 640 285','两组三角形按不同顺序应用变换，编号与颜色共同追踪三个顶点');
      if(document.body.classList.contains('screen-deck')&&stacked){
        let secondStage=$('symmetry-second');if(!secondStage){secondStage=document.createElement('div');secondStage.id='symmetry-second';secondStage.className='stage symmetry-stage';$('symmetry-graph').after(secondStage);}
        $('symmetry-graph').innerHTML=svg(`${triangle(left,160)}<text x="160" y="261" text-anchor="middle" font-size="24" fill="var(--diagram-muted,#61736c)">先 A，后 B</text>`,'0 0 320 285','先 A 后 B');
        secondStage.innerHTML=svg(`${triangle(right,160)}<text x="160" y="261" text-anchor="middle" font-size="24" fill="var(--diagram-muted,#61736c)">先 B，后 A</text>`,'0 0 320 285','先 B 后 A');
      }else $('symmetry-second')?.remove();
    }
    function update(){const ba=M.d3mul(B,A),ab=M.d3mul(A,B);$('sym-readout').innerHTML=`<div>${M.d3labels[B]} ∘ ${M.d3labels[A]} = ${M.d3labels[ba]}<small>先 A，后 B 的总变换</small></div><div>${M.d3labels[A]} ∘ ${M.d3labels[B]} = ${M.d3labels[ab]}<small>先 B，后 A 的总变换</small></div>`;
      setStatus(ba===ab?'<strong>这两个操作可交换。</strong> 这只说明当前这一对相等；要证明群交换，需对所有元素对成立。':'<strong>两种顺序得到不同结果。</strong> 因而 D₃ 不是交换群；但它仍然满足结合律。',false);draw();}
    function transformed(points,g,p){
      const flip=g>=3,k=g%3;let fp=flip?(k?Math.min(1,2*p):p):0,rp=flip&&k?Math.max(0,2*p-1):p;
      const theta=2*Math.PI*k/3*rp,c=Math.cos(theta),s=Math.sin(theta);
      return points.map(([x,y])=>{const xx=x*(flip?Math.cos(Math.PI*fp):1);return [c*xx+s*y,-s*xx+c*y];});
    }
    const setBusy=v=>{busy=v;$('sym-a').disabled=v;$('sym-b').disabled=v;$('sym-play').disabled=v;};
    $('sym-play').onclick=async()=>{
      if(busy)return;setBusy(true);const route=current;draw(base,base);$('sym-step').textContent='第 1 步：第一组做 A，第二组做 B';
      if(!await animate(1000,p=>draw(transformed(base,A,p),transformed(base,B,p))))return;
      if(current!==route)return;$('sym-step').textContent='第 2 步：第一组再做 B，第二组再做 A';
      const left=positions(A),right=positions(B);
      if(!await animate(1000,p=>draw(transformed(left,B,p),transformed(right,A,p))))return;
      if(current!==route)return;update();$('sym-step').textContent='比较两个终态中的顶点编号';setBusy(false);
    };
    $('sym-a').onchange=e=>{A=+e.target.value;$('sym-step').textContent='';update();};$('sym-b').onchange=e=>{B=+e.target.value;$('sym-step').textContent='';update();};onResize=()=>draw(displayedLeft,displayedRight);update();
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
      $('axiom-checks').innerHTML=checks.map(([name,pass,note])=>`<div class="axiom-check" data-verdict="${pass===null?'pending':pass?'pass':'fail'}"><b>${name}</b><span class="sr-only">${pass===null?'待定义':pass?'成立':'不成立'}</span><em class="property-mark" aria-hidden="true">${pass===null?'—':pass?'✓':'✕'}</em><small>${note}</small></div>`).join('');
      const [a,b]=selected,c=op(a,b);let detail=E.includes(c)?'结果仍在所选集合内。':'结果不在所选集合内，因此不封闭。';if(c===data.identity)detail+=` ${fmt(a)} 与 ${fmt(b)} ${op(b,a)===data.identity?'互为双侧逆元。':'只满足当前方向的等式。'}`;
      $('table-readout').innerHTML=`<div class="formula">${model.format(a,b,c)}</div>${detail}`;$('example-note').textContent=key==='unit8'?'每个元素平方均为单位元，因此四个元素都等于自己的逆元。':model.note;
      let status=data.isGroup?`<strong>是群。</strong> ${data.commutative?'也是交换群：表关于主对角线对称。':'不是交换群：例如 r ∘ s ≠ s ∘ r。'}`:'<strong>不是群。</strong> 必须同时满足定义的全部要求。';
      if(data.associativeWitness){const [x,y,z,left,right]=data.associativeWitness;status+=`<br>反例：(${fmt(x)} − ${fmt(y)}) − ${fmt(z)} = ${fmt(left)}；${fmt(x)} − (${fmt(y)} − ${fmt(z)}) = ${fmt(right)}。`;}
      setStatus(status,!data.isGroup);
    }
    $('group-model').onchange=e=>{key=e.target.value;selected=key==='nonzero6'?[2,3]:key==='mul6'?[0,1]:key==='unit5'?[2,3]:key==='d3'?[1,3]:[M.model(key).elements[0],M.model(key).elements[0]];update();};
    $('cayley').onclick=e=>{const b=e.target.closest('button');if(b){selected=[+b.dataset.left,+b.dataset.right];update();$('cayley').querySelector(`[data-left="${selected[0]}"][data-right="${selected[1]}"]`).focus({preventScroll:true});}};update();
  }

  function renderProperties(){
    let chosen=0,step=-1;
    const proofs=[
      {name:'单位元唯一',assumption:'设 e 和 f 都是 G 的双侧单位元。',goal:'结论：e = f',steps:[['e','从 e 开始。'],['e = ef','f 是右单位元，所以 ef = e。'],['e = ef = f','e 是左单位元，所以 ef = f。单位元只能有一个。']]},
      {name:'逆元唯一',assumption:'设 b 和 c 都是 a 的逆元，即 ab = ba = ac = ca = e。',goal:'结论：b = c',steps:[['b','从 b 开始。'],['b = be','右侧乘单位元。'],['b = b(ac)','因为 ac = e。'],['b = (ba)c','只移动括号：结合律。'],['b = ec','因为 ba = e。'],['b = c','左侧单位元不改变 c。逆元唯一。']]},
      {name:'乘积的逆',assumption:'对任意 a, b ∈ G，提出候选逆元 b⁻¹a⁻¹，并检验两侧。',goal:'结论：(ab)⁻¹ = b⁻¹a⁻¹',steps:[['(ab)(b⁻¹a⁻¹)','把候选逆元接在 ab 右侧。'],['a(bb⁻¹)a⁻¹','结合律；因子的顺序未变。'],['aea⁻¹ = aa⁻¹ = e','先消去 b，再消去 a。'],['(b⁻¹a⁻¹)(ab)','还要检查另一侧。'],['b⁻¹(a⁻¹a)b = b⁻¹eb = e','结合律与逆元性质给出单位元。'],['(ab)⁻¹ = b⁻¹a⁻¹','两侧都还原 e，再用逆元唯一性。']]},
      {name:'消去律',assumption:'设 ab = ac。在等式两侧同时左乘 a⁻¹。',goal:'结论：b = c；右消去同理',steps:[['ab = ac','已知条件。'],['a⁻¹(ab) = a⁻¹(ac)','两边同一侧乘同一个元素。'],['(a⁻¹a)b = (a⁻¹a)c','结合律。'],['eb = ec','使用 a⁻¹a = e。'],['b = c','使用单位元性质，得到左消去律。']]},
      {name:'解群方程',assumption:'对给定 a, b ∈ G，分别求解 ax = b 和 ya = b。',goal:'x = a⁻¹b；y = ba⁻¹',steps:[['ax = b','先解未知元在右侧的方程。'],['a⁻¹(ax) = a⁻¹b','左乘 a⁻¹，抵消位于左侧的 a。'],['x = a⁻¹b','结合律和单位元性质；代回检验成立。'],['ya = b','再解未知元在左侧的方程。'],['(ya)a⁻¹ = ba⁻¹','这次要右乘 a⁻¹。'],['y = ba⁻¹','代回检验成立；消去律保证两个解各自唯一。']]}
    ];
    proofs.splice(2,0,{name:'逆元的逆元',assumption:'设 G 为群，a ∈ G。',goal:'结论：(a⁻¹)⁻¹ = a',steps:[['a⁻¹a = aa⁻¹ = e','a 满足作为 a⁻¹ 的逆元的两侧等式。'],['(a⁻¹)⁻¹ = a','由逆元唯一性，a⁻¹ 的逆元就是 a。']]});
    const statements=[
      '定理 1.2.1(1)：设 G 为群，则 G 的单位元唯一。也就是说，若 e、f 都满足对每个 a ∈ G 有 ea = ae = a、fa = af = a，那么 e = f。',
      '定理 1.2.1(2)：设 G 为群，e 为单位元。对每个 a ∈ G，它的逆元唯一。也就是说，若 ab = ba = e 且 ac = ca = e，则 b = c。',
      '定理 1.2.1(4)：设 G 为群。对任意 a、b ∈ G，乘积 ab 的逆元为 b⁻¹a⁻¹，即 (ab)⁻¹ = b⁻¹a⁻¹。逆元的因子次序必须反转。',
      '定理 1.2.1(5)：设 G 为群。对任意 a、b、c ∈ G，若 ab = ac 或 ba = ca，则 b = c。这分别是左消去律和右消去律。',
      '定理 1.2.2：设 G 为群。对任意 a、b ∈ G，方程 ax = b 和 ya = b 在 G 中各有唯一解，分别为 x = a⁻¹b、y = ba⁻¹。'
    ];
    statements.splice(2,0,'定理 1.2.1(3)：设 G 为群。对任意 a ∈ G，(a⁻¹)⁻¹ = a。');
    scene.innerHTML=`<div id="proof-tabs" class="controls proof-options"></div><p id="proof-assumption" class="proof-conditions"></p><div id="proof-board" class="proof-board stage" aria-live="polite"></div><div class="controls"><button type="button" id="proof-back">← 上一步</button><button type="button" id="proof-next" class="primary">下一步 →</button><span id="proof-count" class="hint"></span></div><div id="status" class="status-strip"></div><details class="mini-proof"><summary>另外两条需要记住的运算规则</summary><p>逆元的逆还是自己：(a⁻¹)⁻¹ = a，因为 a 和 a⁻¹ 互为逆元。<br>同一个元素的幂满足 aᵐaⁿ = aᵐ⁺ⁿ、(aᵐ)ⁿ = aᵐⁿ。但对于不同元素，(ab)ⁿ = aⁿbⁿ 一般需要 ab = ba；不能仅凭结合律这样拆开。</p></details>`;
    function update(){const p=proofs[chosen];$('proof-tabs').innerHTML=proofs.map((x,i)=>`<button type="button" data-proof="${i}" aria-pressed="${i===chosen}">${x.name}</button>`).join('');$('proof-assumption').textContent=step<0?'':p.assumption;$('proof-assumption').hidden=step<0;
      $('proof-board').innerHTML=step<0?`<div class="label">定理阐述</div><p class="theorem-statement">${statements[chosen]}</p>`:`<div class="label">${p.goal}</div><div class="expression">${p.steps[step][0]}</div><div class="reason">${p.steps[step][1]}</div><div class="proof-track" aria-hidden="true">${p.steps.map((_,i)=>`<span class="${i<=step?'done':''}"></span>`).join('')}</div>`;
      $('proof-back').disabled=step<0;$('proof-back').textContent=step===0?'← 返回定理':'← 上一步';$('proof-next').textContent=step<0?'开始证明 →':'下一步 →';$('proof-next').disabled=step===p.steps.length-1;$('proof-count').textContent=step<0?'先读清条件与结论':`${step+1} / ${p.steps.length}`;
      setStatus(step<0?'先确认群的假设和要证明的结论，再开始证明。':step===p.steps.length-1?'<strong>证明完成。</strong> 回顾刚才哪些地方用了结合律、单位元或逆元。':'<strong>先预测，再翻一步。</strong> 当前的等式能用哪条公理继续化简？');
    }
    $('proof-tabs').onclick=e=>{const b=e.target.closest('button');if(b){chosen=+b.dataset.proof;step=-1;update();}};$('proof-back').onclick=()=>{step--;update();};$('proof-next').onclick=()=>{step++;update();};update();
  }

  function renderQuiz(){window.TextbookExercises.render(scene,bookId);}
  window.CourseLanguage?.add({'成立':'Satisfied','不成立':'Not satisfied','待定义':'Not yet defined'});
  window.LessonBook={id:bookId,title:book.title,titleEn:bookId==='1.1'?'Equivalence relations and partitions':'The concept of a group',navigate(id){const index=sections.findIndex(s=>s.id===id);if(index>=0)show(index);}};
  window.CourseLanguage?.add({'逆元的逆元':'The inverse of an inverse','设 G 为群，a ∈ G。':'Let G be a group and a ∈ G.','a 满足作为 a⁻¹ 的逆元的两侧等式。':'The element a satisfies both inverse equations for a⁻¹.','由逆元唯一性，a⁻¹ 的逆元就是 a。':'By uniqueness, a is the inverse of a⁻¹.','定理 1.2.1(3)：设 G 为群。对任意 a ∈ G，(a⁻¹)⁻¹ = a。':'Theorem 1.2.1(3): for every a in a group G, (a⁻¹)⁻¹ = a.'});
  const initial=sections.findIndex(s=>s.id===legacyAnchor);
  show(initial>=0?initial:0);
})();
