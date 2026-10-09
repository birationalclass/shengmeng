import {installProofWorlds} from './proof-worlds.js?v=20261010-linear-77';
import {installTheoremTarget} from './theorem-target.js?v=20261010-linear-77';
import {createNodeEditor} from './node-editor.js?v=20261010-linear-77';
import {installWorkspace} from './workspace.js?v=20261010-linear-77';
import {installAtlasDock} from './atlas-dock.js?v=20261010-linear-77';
import {installLeanLineCounts} from './line-counts.js?v=20261010-linear-77';
import {english,installLanguage} from './i18n.js?v=20261010-linear-77';
import {statementPanel,escapeHTML} from './theorem-statements.js?v=20261010-linear-77';


const audit=await fetch('audit.json?v=20261010-linear-77').then(r=>{if(!r.ok)throw Error('Audit unavailable');return r.json();});
const text=(zh,en)=>english?en:zh;
if(audit.mainTheoremVerified!==false||audit.targetVerified!==false)throw Error('Unexpected target status');
const raw=[audit.main,...audit.nodes];
for(const n of raw){if(['done','conditional'].includes(n.status)&&!audit.declarations[n.decl]?.verified)throw Error('Missing checked declaration '+n.decl);}
const nodes=raw.map((n,i)=>({...n,title:n.titles[english?1:0],formula:'',x:30+(i%3)*320,y:60+Math.floor(i/3)*180}));
const root=nodes[0];
const byId=new Map(nodes.map(n=>[n.id,n]));let current='lemma',nodeEditor=null,atlasDock=null,worlds=null,tab='overview';const backstack=[],future=[];
function showSource(n){const el=document.querySelector('#sourcePanel');if(!n.decl){el.innerHTML=`<p class="notice">${text('完整目标还没有经过验证的最终 Lean 声明。','The complete target has no verified final Lean declaration yet.')}</p><ul>${audit.remaining.map(r=>`<li>${escapeHTML(r[english?1:0])}</li>`).join('')}</ul>`;return;}
 el.innerHTML=`<div class="source-name">${escapeHTML(n.decl)}</div>${n.status==='pending'?`<p class="notice">${text('这是尚未证明的目标定义；编译该定义不等于证明定理。','This is an unproved target definition; compiling it does not prove the theorem.')}</p>`:''}<p>${n.lines} ${text('行源码，含注释与空行','source lines, including comments and blanks')}</p><div class="actions"><a class="button small" href="source/${n.file}" download>${text('下载完整源码','Download full source')}</a><a class="button small" href="https://github.com/birationalclass/shengmeng/blob/main/formalization/linear/source/${n.file}" target="_blank">GitHub ↗</a></div><pre class="source-code"><code>${escapeHTML(n.formalType)}</code></pre><p>SHA-256: <code>${escapeHTML(n.sha256)}</code></p>`;
 fetch('source/'+n.file).then(r=>r.text()).then(source=>{if(current===n.id)el.querySelector('code').textContent=source;});
}
function detail(){const n=byId.get(current);document.querySelector('#detailHeader').innerHTML=`<div class="detail-title"><span class="pill ${n.status}">${['done','conditional'].includes(n.status)?'✓':'○'} ${['done','conditional'].includes(n.status)?text('Lean 已验证 · 查看条件','Lean verified · inspect hypotheses'):text('尚未完成','Unfinished')}</span><h2>${escapeHTML(n.title)}</h2></div>`;
 document.querySelector('#overviewPanel').innerHTML=statementPanel(n,english);
 document.querySelector('#stepsPanel').innerHTML=n.id==='lemma'?`<p>${text('各引理可独立查看；最终目标仅使用它实际需要的证明步骤。','Inspect each lemma independently; the final goal uses only its actual supporting proof steps.')}</p>${audit.nodes.map(c=>`<button class="dep-link" data-select="${c.id}">${escapeHTML(c.titles[english?1:0])}<span>${['done','conditional'].includes(c.status)?'✓':'○'}</span></button>`).join('')}`:`<p>${escapeHTML(n.scope[english?1:0])}</p><p>${text('点击 Lean 源码查看实际证明；网页本身不执行 Lean。','Read the Lean source for the actual proof; this webpage does not run Lean.')}</p>`;
 showSource(n);document.querySelector('#back').disabled=!backstack.length;document.querySelector('#forward').disabled=!future.length;document.querySelector('#editorSelect').value=current;
}
function select(id,save=true){if(!byId.has(id))return;if(save&&id!==current){backstack.push(current);future.length=0;}current=id;detail();document.querySelectorAll('[data-node]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.node===id)));nodeEditor?.selectionChanged();}
const graph=document.querySelector('#graph'),svg=document.querySelector('#edges');
for(const n of nodes){const card=document.createElement('button');card.className='node '+n.status;card.dataset.node=n.id;card.type='button';card.onclick=()=>select(n.id);graph.append(card);}
for(const n of nodes)for(const id of n.deps){const edge=document.createElementNS('http://www.w3.org/2000/svg','path');edge.classList.add('edge');edge.dataset.from=id;edge.dataset.to=n.id;edge.innerHTML='<title>Proof-plan dependency; an open geometric step is not a kernel-verified premise.</title>';svg.append(edge);}
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
const snapshot={files:audit.files,declarations:audit.declarations,sourceRanges:audit.sourceRanges};
installLeanLineCounts({snapshot,nodes});
function renderEvidence(){document.querySelector('#evidenceContent').innerHTML=`<p class="notice">${text('完整线性定理尚未证明。坐标目标已定义；已验证的辅助结果不能替代尚未构造的几何输入。','The full Linearity Theorem is not proved. The coordinate target is defined; checked helpers do not discharge the open geometric inputs.')}</p><p>${audit.verifiedTheoremCount} ${text('条定理证明；','theorem proofs; ')}${audit.definitionCount} ${text('个定义（不计作证明）。','definitions (not proofs).')}</p><p>Lean ${audit.lean} · mathlib <code>${audit.mathlib}</code><br>${audit.checkedAt}</p><p>${text('已核验声明的公理范围：','Axioms used by audited declarations: ')}${audit.allowedAxioms.join(' · ')}. ${text('无 sorryAx 或自定义公理。','No sorryAx or custom axioms.')}</p><p>${text('对应原稿指纹：','Manuscript SHA-256: ')}<code>${audit.manuscript.sha256}</code></p><div class="actions"><a class="button" href="verification.txt">${text('完整日志','Build and audit log')} ↗</a><a class="button" href="full-audit.json">${text('全声明审计','All-declaration audit')} ↗</a><a class="button" href="linear-lean.zip" download>${text('可复现 Lean 工程','Reproducible Lean project')} ↓</a></div><h3>${text('仍待完成','Remaining obligations')}</h3><ul>${audit.remaining.map(r=>`<li>${escapeHTML(r[english?1:0])}</li>`).join('')}</ul>`;}
renderEvidence();detail();
document.querySelector('#originalContent').innerHTML=statementPanel(root,english);
window.addEventListener('languagechange',()=>{document.querySelector('#originalContent').innerHTML=statementPanel(root,english);});
document.querySelector('#fullscreen').onclick=()=>document.fullscreenElement?document.exitFullscreen():document.documentElement.requestFullscreen();
document.querySelector('#expandGraph').onclick=()=>{document.body.classList.toggle('atlas-expanded');document.querySelector('#expandGraph').setAttribute('aria-pressed',String(document.body.classList.contains('atlas-expanded')));};
document.querySelector('[data-view="2d"]').onclick=()=>worlds.render();document.querySelector('[data-view="3d"]').hidden=true;
window.linearUI={worlds,nodeEditor,nodes,audit,selected:()=>current};
