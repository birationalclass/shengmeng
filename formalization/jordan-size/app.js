import {installProofWorlds} from './proof-worlds.js?v=20261005-jordan-chains-4';
import {installTheoremTarget} from './theorem-target.js?v=20261005-jordan-chains-4';
import {createNodeEditor} from './node-editor.js?v=20261005-jordan-chains-4';
import {installWorkspace} from './workspace.js?v=20261005-jordan-chains-4';
import {installAtlasDock} from './atlas-dock.js?v=20261005-jordan-chains-4';
import {installLeanLineCounts} from './line-counts.js?v=20261005-jordan-chains-4';
import {english,installLanguage} from './i18n.js?v=20261005-jordan-chains-4';
import {statementPanel,escapeHTML} from './theorem-statements.js?v=20261005-jordan-chains-4';
import {formulas} from './formulas.js?v=20261005-jordan-chains-4';

const audit=await fetch('audit.json?v=20261005-jordan-chains-4').then(r=>{if(!r.ok)throw Error('Audit unavailable');return r.json();});
if(audit.targetVerified!==true||audit.nodes.some(n=>!n.verified))throw Error('Unexpected audit status');
const text=(zh,en)=>english?en:zh;
const mul='<math display="block"><mrow><msup><mi>N</mi><msub><mi>i</mi><mn>1</mn></msub></msup><mo>×</mo><mo>⋯</mo><mo>×</mo><msup><mi>N</mi><msub><mi>i</mi><mi>r</mi></msub></msup><mo>→</mo><msup><mi>N</mi><mrow><msub><mi>i</mi><mn>1</mn></msub><mo>+</mo><mo>⋯</mo><mo>+</mo><msub><mi>i</mi><mi>r</mi></msub></mrow></msup></mrow></math>';
const originalLemma11={id:'lemma',title:'Lemma 1.1 · '+text('对数与 Jordan 链','Logarithms and Jordan chains'),titles:['Lemma 1.1 · 对数与 Jordan 链','Lemma 1.1 · Logarithms and Jordan chains'],status:'done',decl:audit.main.declaration,file:audit.main.file,lines:audit.main.lines,sha256:audit.main.sha256,formalType:audit.main.formalType,deps:audit.rootSteps,
 compactSetup:['有理分次空间、可逆算子及等变多重线性映射。','Rational graded spaces, invertible operators, equivariant multilinear maps.'],
 compactResult:['幺幂部分保持乘法；对数满足 Leibniz 公式，保留 Jordan 块信息。','Multiplicative unipotent part; Leibniz logarithm and Jordan block identities.'],
 setup:[`<p>设 N⁰,…,Nⁿ 为非零有限维有理向量空间，Nⁿ=ℚ。对每组次数之和不超过 n 的指标，给定多重线性映射：</p>${mul}<p>每个次数上给定可逆有理线性算子 𝒯，保持这些映射；顶次 𝒯=d𝓘，d∈ℚ×。空间和映射扩张到 ℝ 或 ℂ。写 𝒯=𝒯ₛ𝒯ᵤ，𝒩=log 𝒯ᵤ。此引理不要求正性或完美配对。</p>`,`<p>Let N⁰,…,Nⁿ be nonzero finite-dimensional rational vector spaces, with Nⁿ=ℚ. For each tuple of degrees summing to at most n, specify a multilinear map:</p>${mul}<p>In each degree let 𝒯 be an invertible rational linear operator preserving these maps, with 𝒯=d𝓘 on Nⁿ, d∈ℚ×. Extend spaces and maps to ℝ or ℂ. Write 𝒯=𝒯ₛ𝒯ᵤ and 𝒩=log 𝒯ᵤ. Positivity and perfect pairings are not required.</p>`],
 result:[`<ol><li>exp(ℓ𝒩)=𝒯ᵤ^ℓ；𝒯ᵤ−𝓘=𝒩Q(𝒩)，其中 Q(𝒩)=Σⱼ≥₀𝒩ʲ/(j+1)! 是可逆的有限和。</li><li>对每个 j≥0，两算子的 j 次幂具有相同的核与像；最大 Jordan 块大小为 1+max{j:𝒩ʲ≠0}。</li><li>𝒯ᵤ 保持每个给定多重线性映射；𝒩 满足相应的多重 Leibniz 公式；顶次 𝒯ᵤ=𝓘。</li><li>取任意正整数次幂 𝒯ᵃ 时，对数变成 a𝒩，所有 Jordan 块大小保持。</li></ol>`,`<ol><li>exp(ℓ𝒩)=𝒯ᵤ^ℓ and 𝒯ᵤ−𝓘=𝒩Q(𝒩), where Q(𝒩)=Σⱼ≥₀𝒩ʲ/(j+1)! is a finite invertible sum.</li><li>For every j≥0, the j-th powers have identical kernels and images; the largest Jordan block has size 1+max{j:𝒩ʲ≠0}.</li><li>𝒯ᵤ preserves every specified multilinear map; 𝒩 satisfies its multilinear Leibniz identity; 𝒯ᵤ=𝓘 in the top degree.</li><li>For any positive integer a, replacing 𝒯 by 𝒯ᵃ replaces 𝒩 by a𝒩 and preserves all Jordan block sizes.</li></ol>`],
 scope:['整合声明与标量扩张桥梁已通过 Lean 内核。Jordan 块以广义特征空间的消去指数与完整核增长表述，不构造显式 Jordan 基。','The integrated declaration and scalar-extension bridge passed the Lean kernel. Jordan sizes use generalized-eigenspace annihilation and the full kernel-growth profile; no explicit Jordan basis is constructed.']};
const root={...audit.rootPresentation,id:'lemma',title:audit.rootPresentation.titles[english?1:0],status:'done',decl:audit.main.declaration,file:audit.main.file,lines:audit.main.lines,sha256:audit.main.sha256,formalType:audit.main.formalType,deps:audit.rootSteps};
const nodes=[root,...audit.nodes.map((n,i)=>({...n,...(n.id==='lemma11'?{setup:originalLemma11.setup,result:originalLemma11.result}:{}),decl:n.declaration,titles:n.title,title:n.title[english?1:0],status:'done',deps:n.deps||[],compactSetup:n.compactSetup||n.setup,compactResult:n.compactResult||n.result,formula:formulas[n.id],x:30+i*320,y:150}))];
const byId=new Map(nodes.map(n=>[n.id,n]));let current='lemma',nodeEditor=null,atlasDock=null,worlds=null,tab='overview';const backstack=[],future=[];
function showSource(n){const el=document.querySelector('#sourcePanel');if(!n.decl){el.innerHTML=`<p class="notice">${text('完整目标还没有经过验证的最终 Lean 声明。','The complete target has no verified final Lean declaration yet.')}</p><ul>${audit.remaining.map(r=>`<li>${escapeHTML(r[english?1:0])}</li>`).join('')}</ul>`;return;}
 el.innerHTML=`<div class="source-name">${escapeHTML(n.decl)}</div><p>${n.lines} ${text('行源码，含注释与空行','source lines, including comments and blanks')}</p><div class="actions"><a class="button small" href="lean/${n.file}" download>${text('下载完整源码','Download full source')}</a><a class="button small" href="https://github.com/birationalclass/shengmeng/blob/main/formalization/jordan-size/lean/${n.file}" target="_blank">GitHub ↗</a></div><pre class="source-code"><code>${escapeHTML(n.formalType)}</code></pre><p>SHA-256: <code>${escapeHTML(n.sha256)}</code></p>`;
 fetch('lean/'+n.file).then(r=>r.text()).then(source=>{if(current===n.id)el.querySelector('code').textContent=source;});
}
function detail(){const n=byId.get(current);document.querySelector('#detailHeader').innerHTML=`<div class="detail-title"><span class="pill ${n.status}">${n.status==='done'?'✓':'○'} ${n.status==='done'?text('Lean 已验证','Lean verified'):text('尚未完成','Unfinished')}</span><h2>${escapeHTML(n.title)}</h2></div>`;
 document.querySelector('#overviewPanel').innerHTML=statementPanel(n,english);
 document.querySelector('#stepsPanel').innerHTML=n.id==='lemma'?`<p>${text('各引理可独立查看；最终目标仅使用它实际需要的证明步骤。','Inspect each lemma independently; the final goal uses only its actual supporting proof steps.')}</p>${audit.nodes.map(c=>`<button class="dep-link" data-select="${c.id}">${escapeHTML(c.title[english?1:0])}<span>✓</span></button>`).join('')}`:`<p>${escapeHTML(n.scope[english?1:0])}</p><p>${text('点击 Lean 源码查看实际证明；网页本身不执行 Lean。','Read the Lean source for the actual proof; this webpage does not run Lean.')}</p>`;
 showSource(n);document.querySelector('#back').disabled=!backstack.length;document.querySelector('#forward').disabled=!future.length;document.querySelector('#editorSelect').value=current;
}
function select(id,save=true){if(!byId.has(id))return;if(save&&id!==current){backstack.push(current);future.length=0;}current=id;detail();document.querySelectorAll('[data-node]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.node===id)));nodeEditor?.selectionChanged();}
const graph=document.querySelector('#graph'),svg=document.querySelector('#edges');
for(const n of nodes){const card=document.createElement('button');card.className='node '+n.status;card.dataset.node=n.id;card.type='button';card.onclick=()=>select(n.id);graph.append(card);}
for(const n of nodes)for(const id of n.deps){const edge=document.createElementNS('http://www.w3.org/2000/svg','path');edge.classList.add('edge');edge.dataset.from=id;edge.dataset.to=n.id;edge.innerHTML='<title>Verified supporting declaration; inspect the exact Lean type and imports.</title>';svg.append(edge);}
document.addEventListener('click',e=>{const b=e.target.closest('[data-select]');if(b)select(b.dataset.select);});
document.querySelectorAll('[data-tab]').forEach(button=>button.onclick=()=>{tab=button.dataset.tab;document.querySelectorAll('[data-tab]').forEach(b=>b.setAttribute('aria-selected',String(b===button)));for(const id of ['overview','steps','source'])document.getElementById(id+'Panel').hidden=id!==tab;});
document.querySelector('#back').onclick=()=>{if(backstack.length){future.push(current);select(backstack.pop(),false);}};
document.querySelector('#forward').onclick=()=>{if(future.length){backstack.push(current);select(future.pop(),false);}};
const label=document.createElement('label');label.textContent=text('定位节点','Locate node');label.innerHTML+='<select id="editorSelect"></select>';document.querySelector('.graph-toolbar').append(label);
function titles(){for(const n of nodes)n.title=n.titles[english?1:0];document.querySelector('#editorSelect').innerHTML=nodes.map(n=>`<option value="${n.id}">${escapeHTML(n.title)}</option>`).join('');document.querySelector('#editorSelect').value=current;}
titles();installLanguage({onChange(){titles();detail();nodeEditor?.refreshLanguage();atlasDock?.refresh(english);renderEvidence();}});
const uiLabels=()=>{const en=english;const options=[['所选及直接前提','Selected and direct premises'],['全图','Full map'],['所选及全部前提','Selected and all premises'],['仅待完成目标','Unfinished targets only']];document.querySelectorAll('#scope option').forEach((o,i)=>o.textContent=options[i][en?1:0]);document.querySelector('#fullscreen').title=en?'Fullscreen':'全屏显示';document.querySelector('#fullscreen').setAttribute('aria-label',en?'Fullscreen':'全屏显示');document.querySelector('.refuge-back').setAttribute('aria-label',en?'Homepage':'返回主页');for(const [id,zh,eng] of [['back','上一节点','Previous node'],['forward','下一节点','Next node']]){document.getElementById(id).title=en?eng:zh;document.getElementById(id).setAttribute('aria-label',en?eng:zh);}};
uiLabels();window.addEventListener('languagechange',uiLabels);
installWorkspace();atlasDock=installAtlasDock({english});
const target=installTheoremTarget(root);nodeEditor=createNodeEditor({viewport:document.querySelector('.graph-scroll'),graph,svg,nodes,select,selected:()=>current,theoremTarget:target});
worlds=installProofWorlds({nodes,select,selected:()=>current,nodeEditor,theoremTarget:target});
const snapshot={files:audit.files,declarations:Object.fromEntries([audit.main,...audit.nodes].map(n=>[n.declaration,{path:'lean/'+n.file}]))};
installLeanLineCounts({snapshot,nodes});
function renderEvidence(){document.querySelector('#evidenceContent').innerHTML=`<p>${text('引理 1.1–1.3 与推论 1.4 已通过 Lean 内核；Jordan 链为实际线性无关向量，块对应通过全部移位幂核维数验证。','Lemmas 1.1–1.3 and Corollary 1.4 passed the Lean kernel. Chains are explicit independent vectors; block correspondence is checked through all shifted-power kernel dimensions.')}</p><p>Lean ${audit.lean} · mathlib <code>${audit.mathlib}</code></p><p>${text('公理仅为','Axioms:')} <code>${audit.allowedAxioms.join(' · ')}</code>. ${text('未使用 sorryAx。','No sorryAx.')}</p><div class="actions"><a class="button" href="audit.json">${text('独立审计记录','Independent audit record')} ↗</a><a class="button" href="ui-provenance.json">${text('界面复用记录','UI reuse provenance')} ↗</a></div><ul>${[audit.main,...audit.nodes].map(n=>`<li><a href="lean/${n.file}">${n.declaration}</a> · ${n.lines} ${text('行','lines')}<br><code>${n.sha256}</code></li>`).join('')}</ul>`;}
renderEvidence();detail();
document.querySelector('#originalContent').innerHTML=statementPanel(root,english);
window.addEventListener('languagechange',()=>{document.querySelector('#originalContent').innerHTML=statementPanel(root,english);});
document.querySelector('#fullscreen').onclick=()=>document.fullscreenElement?document.exitFullscreen():document.documentElement.requestFullscreen();
document.querySelector('#expandGraph').onclick=()=>{document.body.classList.toggle('atlas-expanded');document.querySelector('#expandGraph').setAttribute('aria-pressed',String(document.body.classList.contains('atlas-expanded')));};
document.querySelector('[data-view="2d"]').onclick=()=>worlds.render();document.querySelector('[data-view="3d"]').hidden=true;
window.jordanUI={worlds,nodeEditor,nodes,audit,selected:()=>current};
