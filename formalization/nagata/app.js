import {installProofWorlds} from './proof-worlds.js?v=20261008-nagata-3';
import {installTheoremTarget} from './theorem-target.js?v=20261008-nagata-3';
import {createNodeEditor} from './node-editor.js?v=20261008-nagata-3';
import {installWorkspace} from './workspace.js?v=20261008-nagata-3';
import {installAtlasDock} from './atlas-dock.js?v=20261008-nagata-3';
import {installLeanLineCounts} from './line-counts.js?v=20261008-nagata-3';
import {english,installLanguage} from './i18n.js?v=20261008-nagata-3';
import {statementPanel,escapeHTML} from './theorem-statements.js?v=20261008-nagata-3';


const audit=await fetch('audit.json?v=20261008-nagata-3').then(r=>{if(!r.ok)throw Error('Audit unavailable');return r.json();});
const text=(zh,en)=>english?en:zh;
if(audit.targetVerified&&!audit.localVerification.passed)throw Error('Missing local kernel evidence');
const complete=await fetch('lean-graph.json?v=20261008-nagata-3').then(r=>{if(!r.ok)throw Error('Complete Lean graph unavailable');return r.json();});
const raw=complete.nodes;
for(const n of raw){if(['done','conditional'].includes(n.status)&&!audit.declarations[n.decl]?.verified)throw Error('Missing checked declaration '+n.decl);}
const nodes=raw.map((n,i)=>({...n,title:n.titles[english?1:0],formula:'',x:30+(i%3)*320,y:60+Math.floor(i/3)*180}));
const root=nodes.find(n=>n.id==='lemma');
const byId=new Map(nodes.map(n=>[n.id,n]));let current='lemma',nodeEditor=null,atlasDock=null,worlds=null,tab='overview';const backstack=[],future=[];
function showSource(n){
 if(Number.isInteger(n.sourceLineStart))fetch('source/'+n.file).then(r=>r.text()).then(code=>{if(current!==n.id)return;const el=document.querySelector('#sourcePanel details code');if(el)el.textContent=code.split('\n').slice(n.sourceLineStart-1,n.sourceLineEnd).join('\n');});
 const path=encodeURI(n.file),label=text('文本定位；源码保持官方版本','Text location; official source preserved');
 document.querySelector('#sourcePanel').innerHTML=`<div class="source-name">${escapeHTML(n.decl)}</div><p>${escapeHTML(label)}: ${escapeHTML(n.file)}:${n.generated?text('编译器辅助：无独立源码区间','Compiler auxiliary: no separate source range'):n.sourceLineStart+'–'+n.sourceLineEnd}</p><div class="actions"><a class="button small" href="source/${path}" download>${text('下载本文件','Download this file')} ↓</a><a class="button small" href="nagata-official-source.zip" download>${text('下载完整工程与依赖','Download the complete project closure')} ↓</a><a class="button small" href="https://github.com/openai/math/blob/${audit.upstream.commit}/lean/${path}#L${n.sourceLineStart}" target="_blank" rel="noopener">${text('官方原文','Official source')} ↗</a></div><pre class="source-code"><code>${escapeHTML(n.formalType)}</code></pre><details><summary>${text('原始证明片段','Original proof excerpt')}</summary><pre class="source-code"><code>${escapeHTML(n.generated?text('此辅助项由编译器生成；请查看所属文件及精确类型。','This auxiliary is compiler generated; inspect its owning file and exact type.'):(n.proofExcerpt||text('正在读取原始源码…','Loading original source…')))}</code></pre></details><details><summary>${text('外部 Lean 依赖','External Lean dependencies')} (${(n.externalDependencies||[]).length})</summary><pre>${escapeHTML((n.externalDependencies||[]).join('\n'))}</pre></details><p>SHA-256: <code>${escapeHTML(n.sha256)}</code></p><p class="notice">${text('源码下载不等同于本地编译或 Comparator 重放；核验状态见验证记录。','Source import is distinct from local compilation and Comparator replay. See the verification evidence for actual status.')}</p>`;
}
function detail(){const n=byId.get(current);document.querySelector('#detailHeader').innerHTML=`<div class="detail-title"><span class="pill ${n.status}">${['done','conditional'].includes(n.status)?'✓':'○'} ${['done','conditional'].includes(n.status)?text('Lean 已验证 · 查看条件','Lean verified · inspect hypotheses'):text('尚未核验','Not checked')}</span><h2>${escapeHTML(n.title)}</h2></div>`;
 document.querySelector('#overviewPanel').innerHTML=statementPanel(n,english);
 document.querySelector('#stepsPanel').innerHTML=n.id==='lemma'?`<p>${text('按论文 §1–§5 组织 24 个实现卡包，覆盖全部项目声明。章节分组是阅读组织；声明内连线来自编译器导出的真实依赖。§6 推论不属于此主定理的 Lean 目标。','Twenty-four implementation packs follow paper §§1–5 and cover every project constant. Section grouping is editorial; declaration dependencies are compiler-exported. Section 6 corollaries are outside this Lean target.')}</p>${audit.nodes.map(c=>`<button class="dep-link" data-select="${c.id}">${escapeHTML(c.titles[english?1:0])}<span>${['done','conditional'].includes(c.status)?'✓':'○'}</span></button>`).join('')}`:`<p>${escapeHTML(n.scope[english?1:0])}</p><p>${text('源码标签展示对应声明和原始证明。各引理的条件以精确 Lean 类型为准。','The source tab displays the corresponding declaration and original proof. Inspect exact Lean types for the hypotheses of each lemma.')}</p>`;
 showSource(n);document.querySelector('#back').disabled=!backstack.length;document.querySelector('#forward').disabled=!future.length;document.querySelector('#editorSelect').value=current;
}
function select(id,save=true){if(!byId.has(id))return;if(save&&id!==current){backstack.push(current);future.length=0;}current=id;detail();document.querySelectorAll('[data-node]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.node===id)));nodeEditor?.selectionChanged();}
const graph=document.querySelector('#graph'),svg=document.querySelector('#edges');
for(const n of nodes){const card=document.createElement('button');card.className='node '+n.status;card.dataset.node=n.id;card.type='button';card.onclick=()=>select(n.id);graph.append(card);}
for(const n of nodes)for(const id of n.deps){const edge=document.createElementNS('http://www.w3.org/2000/svg','path');edge.classList.add('edge');edge.dataset.from=id;edge.dataset.to=n.id;edge.innerHTML='<title>Compiler-exported direct project dependency (type and proof/value).</title>';svg.append(edge);}
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
worlds=installProofWorlds({complete,nodes,select,selected:()=>current,nodeEditor,theoremTarget:target});
const snapshot={files:audit.files,declarations:audit.declarations,sourceRanges:audit.sourceRanges,paperPacks:complete.paperPacks};
installLeanLineCounts({snapshot,nodes});
function renderEvidence(){
 const pin=escapeHTML(audit.upstream.commit),verified=audit.localVerification.passed;
 const status=verified?text('官方固定版本的本地编译与公理审计已通过；Comparator 未在本地重放。','Local compilation and axiom audit passed at the official pinned versions; Comparator was not replayed locally.'):text('官方 Lean 形式化已发布，源码与完整项目依赖已导入。本地最终定理复核尚未完成。','The official Lean formalization is published; its source and complete project dependency closure are imported. Local verification of the final theorem has not been completed.');
 document.querySelector('#evidenceContent').innerHTML=`<p class="notice">${escapeHTML(status)}</p><p>${text('最终声明','Final declaration')}: <code>OAI.Nagata.nagata_conjecture</code><br>${text('原始证明依赖','Original proof closure')}: 117 ${text('个 Lean 文件','Lean files')}<br>${text('固定发布版本','Pinned release')}: <a href="https://github.com/openai/math/tree/${pin}" target="_blank" rel="noopener"><code>${pin}</code></a></p><p>${text('上游环境','Upstream environment')}: Lean ${audit.upstream.lean}; mathlib <code>${audit.upstream.mathlib}</code><br>${verified?'Local: '+escapeHTML(audit.lean)+' · mathlib '+escapeHTML(audit.mathlib):text('本地兼容性检查使用已安装的 Lean 4.35.0-rc3，状态单独记录。','Local compatibility checking uses installed Lean 4.35.0-rc3, with its status recorded separately.')}</p><p>${text('官方 Comparator 配置只允许 propext、Quot.sound、Classical.choice。该配置不是本地公理审计日志；参考声明中的 sorry 是比较目标，未导入证明工程。','The official Comparator configuration permits only propext, Quot.sound and Classical.choice. The configuration is not a local axiom-audit log. Intentional sorry targets in the challenge are reference statements and are not imported by the solution project.')}</p><div class="actions"><a class="button" href="paper.pdf" target="_blank" rel="noopener">PDF ↗</a><a class="button" href="nagata-official-source.zip" download>${text('完整官方源码工程','Complete official source project')} ↓</a><a class="button" href="official-scope.md">${text('官方验证范围','Official formalization scope')} ↗</a><a class="button" href="release-metadata/ComparatorChallenges/Nagata.json">Comparator ↗</a><a class="button" href="display-policy.md">${text('显示规则','Display rules')} ↗</a><a class="button" href="audit.json">${text('本地状态数据','Local status data')} ↗</a><a class="button" href="source-manifest.json">${text('源文件指纹与依赖','Source hashes and imports')} ↗</a></div><p>${text('论文','Paper')}: ${audit.manuscript.pages} ${text('页','pages')}<br>SHA-256: <code>${escapeHTML(audit.manuscript.sha256)}</code></p><p>${text('Disclosure：这是对 OpenAI 已发布材料的导入，证明归属原作者。本页面没有进行独立数学审稿；源码核验、数学对应与 Comparator 状态分别记录。','Disclosure: this module imports materials published by OpenAI; proof credit remains with the original author. This page does not provide independent mathematical refereeing. Source checking, mathematical correspondence and Comparator status are recorded separately.')}</p>`;
 document.querySelector('.completion-status').textContent=verified?text('官方固定版本本地内核核验通过','Locally kernel checked at official pinned versions'):text('官方 Lean 已发布 · 本地复核未完成','Official Lean source published · local check incomplete');
}
renderEvidence();detail();
document.querySelector('#originalContent').innerHTML=statementPanel(root,english);
window.addEventListener('languagechange',()=>{document.querySelector('#originalContent').innerHTML=statementPanel(root,english);});
document.querySelector('#fullscreen').onclick=()=>document.fullscreenElement?document.exitFullscreen():document.documentElement.requestFullscreen();
document.querySelector('#expandGraph').onclick=()=>{document.body.classList.toggle('atlas-expanded');document.querySelector('#expandGraph').setAttribute('aria-pressed',String(document.body.classList.contains('atlas-expanded')));};
document.querySelector('[data-view="2d"]').onclick=()=>worlds.render();document.querySelector('[data-view="3d"]').hidden=true;
window.nagataUI={worlds,nodeEditor,nodes,audit,complete,selected:()=>current,select};

import {installLeanCatalog} from "./lean-catalog.js?v=20261008-nagata-3";
installLeanCatalog({nodes,audit,complete,worlds,select});
