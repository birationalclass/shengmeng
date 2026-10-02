import {installDependencyCurrent} from './dependency-current.js?v=20261002-continuous-1';
import {installTheoremTarget} from './theorem-target.js?v=20261002-statusbar-1&proof=20261002-formal-22';
import {divisorCyclePanel} from './divisor-cycle.js?v=20261002-formal-22';
import {curveDiagramPanel} from './curve-diagram.js?v=20261002-formal-22';
import {installSettings} from './settings.js?v=20261002-statusbar-1&proof=20261002-formal-22';
import {createNodeEditor} from './node-editor.js?v=20261002-bound-rail-1&proof=20261002-formal-22';
import {installWorkspace} from './workspace.js?v=20261002-statusbar-1&proof=20261002-formal-22';
import {english,englishStatuses,translateNodes,installLanguage} from './i18n.js?v=20261002-refuge-1&proof=20261002-formal-22';
import {createSpatialGraph} from './graph-3d.js?v=20261002-statusbar-1&proof=20261002-formal-22';
import {nodes as rawNodes,statusLabels as rawLabels} from './graph-data.js?v=20261002-msmath-8&proof=20261002-formal-22';
const nodes=translateNodes(rawNodes),statusLabels={...(english?englishStatuses:rawLabels)};
document.querySelector('.relation-legend').innerHTML=english?'<b>Selection</b><span>◎ Selected result</span><span>Brighter cards · direct premises</span><span>Standard cards · indirect premises</span><span>Dimmed · unrelated</span>':'<b>选中关系</b><span>◎ 当前结论</span><span>明亮卡片：直接前提</span><span>普通卡片：间接前提</span><span>淡化：非当前依赖</span>';
function renderHome(){
  const home=document.querySelector('.refuge-back');
  home.querySelector('span').textContent=english?'Home':'主页';
  home.setAttribute('aria-label',english?'Go to homepage':'返回主页');
  document.querySelector('.atlas-statusbar').setAttribute('aria-label',english?'Verification status':'验证状态');
}
function renderStatusCounts(){
  const legend=document.querySelector('.atlas-statusbar .legend');
  if(!legend)return;
  legend.querySelector('.completion-status').hidden=nodes.find(n=>n.id==='proper')?.status==='done';
  for(const status of ['done','conditional','assumption','pending']){
    const pill=legend.querySelector('.pill.'+status);
    if(!pill)continue;
    const count=nodes.filter(n=>n.status===status).length;
    const badge=document.createElement('b');
    badge.className='status-count';
    badge.dataset.statusCount=status;
    badge.textContent=String(count);
    pill.append(badge);
    pill.title=english?'All graph nodes in this status, independent of the current filter':'此状态的全图节点数量，与当前筛选无关';
    pill.setAttribute('aria-label',statusLabels[status]+' · '+count+(english?' graph nodes':' 个图谱节点'));
  }
  const total=document.createElement('span');
  total.className='legend-total';
  total.textContent=english?'Full graph · '+nodes.length+' nodes':'全图 · '+nodes.length+' 节点';
  legend.append(total);
}
renderStatusCounts();
const byId = new Map(nodes.map(n=>[n.id,n]));
const graph=document.querySelector('#graph'), svg=document.querySelector('#edges');
const safe=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
let spatial=null,nodeEditor=null;
let selected='proper',history=[],future=[],step=0,activeTab='overview',snapshot=null;
function closure(id,out=new Set()){if(out.has(id))return out;out.add(id);byId.get(id).deps.forEach(d=>closure(d,out));return out;}
function relation(id){if(id===selected)return 'selected';if(byId.get(selected).deps.includes(id))return 'direct';return closure(selected).has(id)?'indirect':'other';}
function depButton(n){return `<button class="dep-link" data-select="${n.id}">${safe(n.title)}<span class="${n.status}">${statusLabels[n.status]}</span></button>`;}
nodes.forEach(n=>{const b=document.createElement('button');b.type='button';b.className=`node ${n.status}`;b.style.left=n.x+'px';b.style.top=n.y+'px';b.dataset.node=n.id;b.setAttribute('aria-label',n.title+' · '+statusLabels[n.status]);b.setAttribute('aria-pressed','false');b.innerHTML=`<b>${safe(n.title)}</b><small class="${n.status}">${statusLabels[n.status]}</small><span class="relation-tag"></span>`;b.addEventListener('click',()=>select(n.id));graph.append(b);});
const graphHeight=Math.max(...nodes.map(n=>n.y))+140;graph.style.minHeight=graphHeight+'px';svg.style.height=graphHeight+'px';
svg.innerHTML='<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="#7997a3"/></marker></defs>';
nodes.forEach(n=>n.deps.forEach(id=>{const d=byId.get(id),p=document.createElementNS('http://www.w3.org/2000/svg','path');let x1=d.x+232,y1=d.y+43,x2=n.x,y2=n.y+43;if(d.x===n.x){x1=d.x+116;y1=d.y+87;x2=n.x+116;y2=n.y;}
const bend=Math.max(40,Math.abs(x2-x1)*.45);p.setAttribute('d',`M${x1},${y1} C${x1+bend},${y1} ${x2-bend},${y2} ${x2},${y2}`);p.setAttribute('marker-end','url(#arrow)');p.classList.add('edge');if(d.status==='assumption')p.classList.add('assumed');p.dataset.from=id;p.dataset.to=n.id;svg.append(p);}));
function paint(){const scope=document.querySelector('#scope').value,chain=closure(selected);graph.querySelectorAll('.node').forEach(b=>{const n=byId.get(b.dataset.node);b.setAttribute('aria-pressed',String(n.id===selected));const dim=scope==='path'?!chain.has(n.id):scope==='open'?!['assumption','pending'].includes(n.status):!chain.has(n.id);b.classList.toggle('dimmed',dim);b.dataset.relation=relation(n.id);b.querySelector('.relation-tag').textContent=({selected:'当前结论',direct:'直接前提',indirect:'间接前提',other:'非当前依赖'})[relation(n.id)];});svg.querySelectorAll('.edge').forEach(p=>{const on=chain.has(p.dataset.from)&&chain.has(p.dataset.to);p.classList.toggle('active',on);p.style.display=scope==='open'?'none':'';p.style.opacity=scope==='path'&&!on?'0':'';});document.querySelector('#back').disabled=!history.length;document.querySelector('#forward').disabled=!future.length;const picker=document.querySelector('#editorSelect');if(picker)picker.value=selected;if(spatial)spatial.update(selected,scope);if(nodeEditor)nodeEditor.selectionChanged();}
function sourcePanel(n){const el=document.querySelector('#sourcePanel');if(!n.decl){el.innerHTML='<p class="notice">此节点尚无完成的 Lean 几何证明。图中的中文论证不能替代形式化验证。</p><a class="button" href="#paper-'+n.paper+'">阅读原始证明 →</a>';return;}
if(!snapshot){el.innerHTML='<p>正在读取源码快照…</p>';return;}
const source=snapshot.declarations[n.decl];if(!source){el.innerHTML='<p class="error">缺少对应源码，不能展示验证标记。</p>';return;}
el.innerHTML=`<div class="source-name">Negativity.${safe(n.decl)}</div><p class="text-small">${safe(source.path)} · 第 ${source.line} 行</p><div class="actions"><a class="button small" href="source/${safe(source.path)}" download>下载源码</a><a class="button small" href="https://github.com/birationalclass/shengmeng/blob/main/formalization/negativity/source/${safe(source.path)}#L${source.line}" target="_blank" rel="noopener">GitHub 定位 ↗</a></div><pre class="source-code"><code>${source.code.split('\n').map((l,i)=>`<span class="source-line"><em>${i+source.line}</em>${safe(l)}</span>`).join('')}</code></pre>${(n.related||[]).map(name=>{const r=snapshot.declarations[name];return `<details><summary>${safe(name)}</summary><pre class="source-code"><code>${safe(r.code)}</code></pre></details>`;}).join('')}<p>参数假设请看定理完整类型。依赖仅含 Lean 常用基础公理，不意味着这些参数假设已从几何得到证明。</p>`;}
function renderStep(){const n=byId.get(selected),s=n.steps[step];document.querySelector('#stepsPanel').innerHTML=`<p class="text-small">${n.decl?'已验证源码的阅读导览':'原始数学证明 / 待完成计划'} · 非实时 Lean 执行</p><div class="stepper"><button class="button small" id="prevStep" ${step===0?'disabled':''}>← 上一步</button><span>${step+1} / ${n.steps.length}</span><button class="button small" id="nextStep" ${step===n.steps.length-1?'disabled':''}>下一步 →</button></div><div class="step-body"><h3>${safe(s[0])}</h3><p>${safe(s[1])}</p>${s[2]?`<div class="step-code">${safe(s[2])}</div>`:''}</div><a class="text-button" href="#paper-${n.paper}">对应原始证明 ↘</a>`;document.querySelector('#prevStep').onclick=()=>{step--;renderStep();};document.querySelector('#nextStep').onclick=()=>{step++;renderStep();};}
function precisePanel(n){if(n.id==='strict')return divisorCyclePanel(n,english);if(n.id==='pullbackdiagram')return curveDiagramPanel(n,english);if(['effdown','pushpull'].includes(n.id))return `<section class="proof-formula"><h3>${english?'Actual geometric identity verified':'实际几何等式已验证'}</h3><div class="formula">π<sub>*</sub>(π<sup>*</sup>D) = D</div><p>${english?'Actual Cartier pullback atlases and Weil cycles are constructed from the Scheme morphism. Codimension-one stalks prove coefficient agreement and degree one; finite real combinations give the R-Cartier identity. No hleft input remains.':'实际 Cartier 拉回图册和 Weil cycle 已由 Scheme 态射构造；余维一 stalk 同构给系数相等与次数一，再对有限实线性组合得到 R-Cartier 推拉等式。不再需要 hleft 输入。'}</p><pre><code>exists_realCartier_pullback_pushforward
exists_realCartier_effectivity_descent</code></pre><h3>${english?'Condition when applying effectivity descent':'应用有效性下降时的条件'}</h3><pre><code>CycleEffective (actualPullbackWeilCycle)</code></pre><p>${english?'Given effective pullback, actual pushforward preserves effectivity and the verified identity recovers D. The projective negativity theorem that supplies effective pullback is still open. Curve intersection projection is a separate open theorem.':'已知实际拉回有效时，真实推出保持有效，再用已验证恒等式恢复 D。提供拉回有效性的射影 negativity 完整几何证明仍待完成；曲线交数的射影公式也是另一个待完成命题。'}</p></section>`;if(!n.precise)return '';const p=n.precise[english?'en':'zh'];return `${curveDiagramPanel(n,english)}<section class="proof-formula"><h3>${english?'Required identity':'需要证明的公式'}</h3><p>${safe(p.setup)}</p><div class="formula">(π<sup>*</sup>D) · Γ = D · π<sub>*</sub>[Γ]</div><p>${safe(p.zero)}</p><div class="formula">(π<sup>*</sup>D) · Γ = 0</div><p>${safe(p.curve)}</p><div class="formula">(π<sup>*</sup>D) · Γ = r (D · C)</div><p>${safe(p.degree)}</p><h3>${english?'Where it is used':'用它证明什么'}</h3><p>${safe(p.use)}</p><h3>${english?'Remaining Cartier compatibility':'剩余的 Cartier 交数兼容性'}</h3><pre><code>hcompat : up (single x 1) =
  down (AlgebraicCycle.map π wx wy (single x 1))</code></pre><p>${english?'Prove this for Cartier generators. Real-span extension and the zero / residue-degree cases are now verified separately.':'只需先对 Cartier 生成元证明它；实线性延伸与零值／次数倍两种情形已分别验证。'}</p><p>${safe(p.gap)}</p><a href="https://stacks.math.columbia.edu/tag/0AYA" target="_blank" rel="noopener">Stacks Project · 42.26.4 ↗</a></section>`;}
function renderDetail(){const n=byId.get(selected);document.querySelector('#detailHeader').innerHTML=`<span class="pill ${n.status}">${statusLabels[n.status]}</span><h2>${safe(n.title)}</h2><p class="statement">${safe(n.statement)}</p><p>${safe(n.scope)}</p>${n.status==='conditional'?`<p class="notice conditional-scope">${english?'Only the implication under the displayed hypotheses has been checked. The missing geometric inputs and the complete negativity lemma remain unproved.':'这里只验证了所列假设下的蕴含。缺失的几何输入与完整 negativity lemma 仍未证明。'}</p>`:''}`;
const unfinished=[...closure(selected)].map(id=>byId.get(id)).filter(n=>n.status==='assumption');
document.querySelector('#overviewPanel').innerHTML=`${precisePanel(n)}${(n.upstream||[]).length?`<h3>${english?"Existing formalized source":"已有形式化源码"}</h3><p>${n.upstream.map(([label,url])=>`<a href="${safe(url)}" target="_blank" rel="noopener">${safe(label)} ↗</a>`).join("<br>")}</p>`:""}<h3>为了得到这个结论，先需要</h3><div class="dep-list">${n.deps.length?n.deps.map(id=>depButton(byId.get(id))).join(''):'<p class="empty">没有其他项目节点；使用 mathlib 基础与下列明确输入。</p>'}</div><h3>${n.status==='assumption'?'尚需建立的几何内容':'当前输入 / 假设'}</h3><ul>${n.inputs.map(s=>`<li>${safe(s)}</li>`).join('')}</ul>${unfinished.length?`<h3>沿这条路径，仍需承认的几何输入 · ${unfinished.length}</h3><p class="notice">琥珀色表示显式假设或待补的几何桥接，不是代码中的新增 axiom。</p><div class="dep-list">${unfinished.map(depButton).join('')}</div>`:'<p class="empty">此依赖链没有未证明的几何输入；定理的定义条件仍须满足。</p>'}<h3>接下来哪些结论使用它</h3><div class="dep-list">${nodes.filter(m=>m.deps.includes(n.id)).map(depButton).join('')||'<span class="text-small">这是当前图谱的最终目标。</span>'}</div>`;
renderStep();sourcePanel(n);paint();}
function select(id,record=true){if(!byId.has(id))return;if(record&&id!==selected){history.push(selected);future=[];}selected=id;step=0;window.history.replaceState(null,'',`#node=${id}`);renderDetail();if(matchMedia('(max-width:760px)').matches)document.body.classList.add('inspector-open');}
document.addEventListener('click',e=>{const b=e.target.closest('[data-select]');if(b)select(b.dataset.select);});
const scopePicker=document.querySelector('#scope');scopePicker.value=localStorage.getItem('formalization-scope')||'direct';
document.querySelector('#back').onclick=()=>{if(history.length){future.push(selected);select(history.pop(),false);}};document.querySelector('#forward').onclick=()=>{if(future.length){history.push(selected);select(future.pop(),false);}};document.querySelector('#scope').onchange=()=>{localStorage.setItem('formalization-scope',scopePicker.value);paint();};
document.querySelectorAll('[data-tab]').forEach(b=>b.onclick=()=>{activeTab=b.dataset.tab;document.querySelectorAll('[data-tab]').forEach(t=>t.setAttribute('aria-selected',String(t===b)));['overview','steps','source'].forEach(t=>document.querySelector('#'+t+'Panel').hidden=t!==activeTab);});
document.querySelector('#expandGraph').onclick=e=>{const expanded=document.querySelector('.atlas').classList.toggle('expanded');e.currentTarget.setAttribute('aria-pressed',String(expanded));e.currentTarget.querySelector('span').textContent=expanded?'恢复分栏':'展开图谱';nodeEditor.show();spatial.show();};
document.querySelector('.pdf-view').addEventListener('toggle',e=>{const f=e.currentTarget.querySelector('iframe');if(e.currentTarget.open&&!f.src)f.src=f.dataset.src;});
if(location.hash.startsWith('#node=')){const id=location.hash.slice(6);if(byId.has(id))selected=id;}
const theoremTarget=installTheoremTarget();
installWorkspace();
installSettings();
const pickerLabel=document.createElement('label');pickerLabel.textContent=english?'Locate node ':'定位节点 ';const editorPicker=document.createElement('select');editorPicker.id='editorSelect';nodes.forEach(n=>{const o=document.createElement('option');o.value=n.id;o.textContent=n.title;editorPicker.append(o);});editorPicker.value=selected;editorPicker.onchange=()=>select(editorPicker.value);pickerLabel.append(editorPicker);document.querySelector('.graph-toolbar').append(pickerLabel);
nodeEditor=createNodeEditor({viewport:document.querySelector('.graph-scroll'),graph,svg,nodes,select,selected:()=>selected,theoremTarget});
spatial=createSpatialGraph({host:document.querySelector('#spatialGraph'),nodes,select,relation,theoremTarget});
document.querySelectorAll('[data-view]').forEach(b=>b.onclick=()=>{const three=b.dataset.view==='3d';localStorage.setItem('formalization-view',b.dataset.view);document.querySelector('#spatialGraph').hidden=!three;document.querySelector('.graph-scroll').hidden=three;document.querySelectorAll('[data-view]').forEach(t=>t.setAttribute('aria-pressed',String(t===b)));if(three)spatial.show();else nodeEditor.show();});
renderDetail();
installLanguage({onChange(){
 renderHome();
 const translated=translateNodes(rawNodes);nodes.forEach((n,i)=>Object.assign(n,translated[i]));Object.assign(statusLabels,english?englishStatuses:rawLabels);
 for(const picker of [editorPicker,document.querySelector('#spatialSelect')])for(const option of picker.options)option.textContent=byId.get(option.value).title;
 pickerLabel.firstChild.nodeValue=english?'Locate node ':'定位节点 ';
 for(const n of nodes)graph.querySelector(`[data-node="${n.id}"]`).setAttribute('aria-label',n.title+' · '+statusLabels[n.status]);
 for(const status of ['done','conditional','assumption']){const pill=document.querySelector('.atlas-statusbar .legend .pill.'+status);pill.setAttribute('aria-label',statusLabels[status]+' · '+nodes.filter(n=>n.status===status).length+(english?' graph nodes':' 个图谱节点'));pill.title=english?'All graph nodes in this status, independent of the current filter':'此状态的全图节点数量，与当前筛选无关';}
 document.querySelector('.legend-total').textContent=english?'Full graph · '+nodes.length+' nodes':'全图 · '+nodes.length+' 节点';
 const detail=document.querySelector('#detail'),scroll=detail.scrollTop;nodeEditor.refreshLanguage();renderDetail();detail.scrollTop=scroll;
}});
renderHome();
if(localStorage.getItem('formalization-view')==='3d')document.querySelector('[data-view="3d"]').click();
fetch('snapshot.json?v=20261002-formal-22').then(r=>{if(!r.ok)throw new Error('HTTP '+r.status);return r.json();}).then(data=>{snapshot=data;sourcePanel(byId.get(selected));document.querySelector('#evidenceContent').innerHTML=`<div class="evidence-grid"><div><b>代码编译通过 ✓</b><small>当前源码快照 · 本地验证</small></div><div><b>${Object.keys(data.declarations).length} 个已编译定理声明（含条件式）</b><small>公理检查无 sorryAx</small></div><div><b>${safe(data.checkedAt)}</b><small>验证日期 · 中国标准时间</small></div></div><p>Lean <code>${safe(data.lean)}</code> · mathlib <code>${safe(data.mathlib.slice(0,12))}</code></p><p>公理依赖：<code>propext · Classical.choice · Quot.sound</code>。没有新增几何公理；未完成内容仍是显式参数或规划节点。</p><div class="actions"><a class="button" href="verification.txt">完整验证日志 ↗</a><a class="button" href="snapshot.json">源码 SHA-256 清单 ↗</a><a class="button" href="source/CheckAxioms.lean">公理检查脚本 ↗</a></div><details><summary>公开源码的指纹</summary><ul class="evidence-list">${data.files.map(f=>`<li><a href="source/${safe(f.path)}">${safe(f.path)}</a><br><code>${safe(f.sha256)}</code></li>`).join('')}</ul></details>`;}).catch(err=>{document.querySelector('#evidenceContent').innerHTML='<p class="error">验证记录加载失败，请刷新或下载工程核查。</p>';document.querySelector('#sourcePanel').innerHTML='<p class="error">源码快照加载失败。</p>';console.error(err);});

document.querySelector('#fullscreen').onclick=()=>{if(document.fullscreenElement)document.exitFullscreen();else document.documentElement.requestFullscreen().catch(()=>document.querySelector('#expandGraph').click());};

installDependencyCurrent({nodes,graph,svg,selected:()=>selected,spatialHost:document.querySelector('#spatialGraph'),english});
