'use strict';
let audit, language = new URLSearchParams(location.search).get('lang') || localStorage.getItem('formalization-language') || 'zh', selected = 'target';
const txt = pair => pair[language === 'en' ? 1 : 0];
const label = (zh, en) => language === 'en' ? en : zh;
const esc = s => s.replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const formulas = {
 log: '<math><mrow><mi>ker</mi><mo>(</mo><msup><mi>L</mi><mi>j</mi></msup><mo>)</mo><mo>=</mo><mi>ker</mi><mo>(</mo><msup><mi>D</mi><mi>j</mi></msup><mo>)</mo><mo>,</mo><mspace width=".5em"/><mi>im</mi><mo>(</mo><msup><mi>L</mi><mi>j</mi></msup><mo>)</mo><mo>=</mo><mi>im</mi><mo>(</mo><msup><mi>D</mi><mi>j</mi></msup><mo>)</mo></mrow></math>',
 product: '<math><mrow><msup><mrow><mo>(</mo><mi>R</mi><mo>−</mo><mi>a</mi><mi>b</mi><mi>I</mi><mo>)</mo></mrow><mrow><mi>p</mi><mo>+</mo><mi>q</mi><mo>−</mo><mn>1</mn></mrow></msup><mi>B</mi><mo>(</mo><mi>x</mi><mo>,</mo><mi>y</mi><mo>)</mo><mo>=</mo><mn>0</mn></mrow></math>',
 flow: '<math><mrow><mi>U</mi><mo>(</mo><mi>s</mi><mo>+</mo><mi>t</mi><mo>)</mo><mo>=</mo><mi>U</mi><mo>(</mo><mi>s</mi><mo>)</mo><mi>U</mi><mo>(</mo><mi>t</mi><mo>)</mo><mo>,</mo><mspace width=".5em"/><mi>U</mi><mo>(</mo><mi>t</mi><mo>)</mo><mi>U</mi><mo>(</mo><mo>−</mo><mi>t</mi><mo>)</mo><mo>=</mo><mi>I</mi></mrow></math>',
 decomposition: '<math><mrow><mi>T</mi><mo>=</mo><mi>S</mi><mi>U</mi><mo>=</mo><mi>U</mi><mi>S</mi><mo>,</mo><mspace width=".5em"/><msup><mrow><mo>(</mo><mi>U</mi><mo>−</mo><mi>I</mi><mo>)</mo></mrow><mi>r</mi></msup><mo>=</mo><mn>0</mn></mrow></math>',
 series: '<math><mrow><mi>exp</mi><mo>(</mo><mi>log</mi><mo>(</mo><mn>1</mn><mo>+</mo><mi>X</mi><mo>)</mo><mo>)</mo><mo>=</mo><mn>1</mn><mo>+</mo><mi>X</mi></mrow></math>'
};
function renderInspector() {
 const pane = document.getElementById('inspector');
 if (selected === 'target') {
  pane.innerHTML = `<p class="unfinished">○ ${label('完整引理尚未通过 Lean 验证','The complete lemma is not Lean verified')}</p><h2>${label('Lemma 1.1 · 对数与 Jordan 链','Lemma 1.1 · Logarithms and Jordan chains')}</h2><h3>⌜ ${label('设 · 条件','Let · Conditions')}</h3><p>${label('有限维有理分次向量空间，给定等变的多重线性乘法。每个次数上 T 可逆；顶次是一维空间，T 在其上作用为非零标量。','Finite-dimensional rational graded spaces with specified equivariant multilinear products. T is invertible in every degree; the top degree is one-dimensional and T acts there by a nonzero scalar.')}</p><p>${label('定义 T=TₛTᵤ，𝒩=log Tᵤ；向量空间和映射扩张到实数或复数。此线性代数引理不要求正性或完美配对。','Write T=TₛTᵤ and 𝒩=log Tᵤ, and extend the spaces and maps to the reals or complexes. This linear algebra lemma does not require positivity or a perfect pairing.')}</p><h3>⇒ ${label('目标 · 结论','Goal · Conclusion')}</h3><ul><li>${label('Tᵤ 保持给定乘法；𝒩 满足每个多重线性映射的 Leibniz 公式。','Tᵤ preserves each specified product; 𝒩 satisfies the corresponding multilinear Leibniz identity.')}</li><li>${label('exp(ℓ𝒩)=Tᵤ^ℓ；Tᵤ−I 与 𝒩 的所有幂具有相同的核与像；顶次 Tᵤ=I。','exp(ℓ𝒩)=Tᵤ^ℓ; powers of Tᵤ−I and 𝒩 have the same kernels and images; Tᵤ=I in the top degree.')}</li><li>${label('最大 Jordan 块大小等于 1+max{j:𝒩^j≠0}，并在取正整数次幂时保持。','The largest Jordan block has size 1+max{j:𝒩^j≠0}, unchanged by taking a positive-integer power.')}</li></ul><h3>${label('仍待完成','Still required')}</h3><ul>${audit.remaining.map(p=>`<li>${esc(txt(p))}</li>`).join('')}</ul><p class="scope">${label('五项辅助结果不是完整引理的验证。此目标暂无已完成的最终 Lean 声明。','Five prerequisites do not constitute verification of the whole lemma. This target has no completed final Lean declaration yet.')}</p>`;
 } else {
  const n = audit.nodes.find(n=>n.id===selected);
  pane.innerHTML = `<p class="verified">✓ ${label('Lean 内核已验证 · 辅助结果','Lean kernel verified · prerequisite')}</p><h2>${esc(txt(n.title))}</h2><h3>⌜ ${label('设 · 条件','Let · Conditions')}</h3><p>${esc(txt(n.setup))}</p><h3>⇒ ${label('则 · 结论','Then · Conclusion')}</h3><p>${esc(txt(n.result))}</p><div class="formula">${formulas[n.id]}</div><p class="scope">${esc(txt(n.scope))}</p><p class="line-count">${n.lines} ${label('行 Lean 源码（含注释与空行）','Lean source lines (including comments and blanks)')}</p><details><summary>${label('精确 Lean 类型','Exact Lean type')}</summary><pre id="formalType"></pre></details><a href="lean/${n.file}">${label('查看完整 Lean 源码','Read the complete Lean source')} ↗</a><details><summary>${label('内核公理与文件校验值','Kernel axioms and file checksum')}</summary><pre>${esc(n.declaration)}\n${esc(audit.allowedAxioms.join(', '))}\nSHA-256: ${n.sha256}</pre></details>`;
  document.getElementById('formalType').textContent = n.formalType;
 }
}
function select(id) { selected=id; document.querySelectorAll('.proof-card').forEach(c=>c.classList.toggle('selected',c.dataset.id===id)); renderInspector(); }
function render() {
 document.documentElement.lang=language==='en'?'en':'zh-CN';
 document.querySelectorAll('[data-zh]').forEach(el=>el.textContent=el.dataset[language==='en'?'en':'zh']);
 document.getElementById('languageToggle').textContent=language==='en'?'中文':'EN';
 document.getElementById('languageToggle').setAttribute('aria-label',label('切换中英文','Switch language'));
 document.getElementById('totalLines').textContent=`${audit.totalLines} Lean ${label('行','lines')}`;
 document.getElementById('targetLines').textContent=`${audit.totalLines} ${label('行','lines')}`;
 document.getElementById('targetLines').title=label('整个模块去重后的源码行数；主目标尚未完成','Deduplicated module source lines; the main target is unfinished');
 document.getElementById('prerequisites').innerHTML=audit.nodes.map(n=>`<button class="proof-card" data-id="${n.id}"><div class="card-head"><span class="badge" aria-label="${label('已验证','Verified')}">✓</span><span>LEAN</span><span class="line-count">${n.lines} ${label('行','lines')}</span></div><h2>${esc(txt(n.title))}</h2><div class="clause"><b>⌜ ${label('设','Let')}</b><p>${esc(txt(n.setup))}</p></div><div class="clause"><b>⇒ ${label('则','Then')}</b><p>${esc(txt(n.result))}</p></div></button>`).join('');
 document.querySelectorAll('.proof-card').forEach(c=>c.onclick=()=>select(c.dataset.id));
 document.getElementById('evidenceText').textContent=label(`五项辅助声明已通过 Lean ${audit.lean} 检查。未使用 sorryAx；公理仅为 propext、Classical.choice、Quot.sound。点击卡片查看精确类型、源码与校验值。`,`Five prerequisite declarations passed Lean ${audit.lean}. No sorryAx is used; axioms are only propext, Classical.choice and Quot.sound. Select a card for its exact type, source and checksum.`);
 select(selected);
}
document.getElementById('languageToggle').onclick=()=>{language=language==='en'?'zh':'en';localStorage.setItem('formalization-language',language);render();};
fetch('audit.json').then(r=>{if(!r.ok)throw Error('Audit unavailable');return r.json();}).then(data=>{audit=data;render();}).catch(()=>{document.getElementById('inspector').textContent=label('审计记录加载失败；不能展示验证状态。','The audit record could not be loaded; verification status cannot be displayed.');});
