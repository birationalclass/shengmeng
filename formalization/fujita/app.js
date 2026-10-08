import {installProofWorlds} from './proof-worlds.js?v=20261008-fujita-1';
import {installTheoremTarget} from './theorem-target.js?v=20261008-fujita-1';
import {createNodeEditor} from './node-editor.js?v=20261008-fujita-1';
import {installWorkspace} from './workspace.js?v=20261008-fujita-1';
import {installAtlasDock} from './atlas-dock.js?v=20261008-fujita-1';
import {installLeanLineCounts} from './line-counts.js?v=20261008-fujita-1';
import {english,installLanguage} from './i18n.js?v=20261008-fujita-1';
import {statementPanel,escapeHTML} from './theorem-statements.js?v=20261008-fujita-1';


const audit=await fetch('audit.json?v=20261008-fujita-1').then(r=>{if(!r.ok)throw Error('Audit unavailable');return r.json();});
const text=(zh,en)=>english?en:zh;
if(audit.mainTheoremVerified!==false||audit.targetVerified!==false)throw Error('Unexpected target status');
const raw=[audit.main,...audit.nodes];
for(const n of raw){if(['done','conditional'].includes(n.status)&&!audit.declarations[n.decl]?.verified)throw Error('Missing checked declaration '+n.decl);}
const nodes=raw.map((n,i)=>({...n,title:n.titles[english?1:0],formula:'',x:30+(i%3)*320,y:60+Math.floor(i/3)*180}));
const root=nodes[0];
const byId=new Map(nodes.map(n=>[n.id,n]));let current='lemma',nodeEditor=null,atlasDock=null,worlds=null,tab='overview';const backstack=[],future=[];
function showSource(n){
 document.querySelector('#sourcePanel').innerHTML=`<p class="notice">${text('尚未取得相应的 Lean 源码；没有本模块的编译或公理审计结果。','The corresponding Lean source has not been obtained; this module has no Lean build or axiom audit result.')}</p><p>${escapeHTML(n.paperReference)}</p><div class="actions"><a class="button small" href="paper.pdf" target="_blank" rel="noopener">${text('阅读官方论文','Read the official manuscript')} ↗</a><a class="button small" href="verification.txt">${text('源码定位记录','Source-discovery record')} ↗</a></div>`;
}
function detail(){const n=byId.get(current);document.querySelector('#detailHeader').innerHTML=`<div class="detail-title"><span class="pill ${n.status}">${['done','conditional'].includes(n.status)?'✓':'○'} ${['done','conditional'].includes(n.status)?text('Lean 已验证 · 查看条件','Lean verified · inspect hypotheses'):text('尚未核验','Not checked')}</span><h2>${escapeHTML(n.title)}</h2></div>`;
 document.querySelector('#overviewPanel').innerHTML=statementPanel(n,english);
 document.querySelector('#stepsPanel').innerHTML=n.id==='lemma'?`<p>${text('沿原稿 Figure 1 阅读五个环节；连线表示论文阅读路径，尚无 Lean 依赖审计。','Follow the five stages in manuscript Figure 1. Edges are manuscript reading paths; no Lean dependency audit is available.')}</p>${audit.nodes.map(c=>`<button class="dep-link" data-select="${c.id}">${escapeHTML(c.titles[english?1:0])}<span>${['done','conditional'].includes(c.status)?'✓':'○'}</span></button>`).join('')}`:`<p>${escapeHTML(n.scope[english?1:0])}</p><p>${text('在源码标签中查看原文定位；相应 Lean 声明待取得。','Use the source tab to locate the manuscript passage; the corresponding Lean declaration is still needed.')}</p>`;
 showSource(n);document.querySelector('#back').disabled=!backstack.length;document.querySelector('#forward').disabled=!future.length;document.querySelector('#editorSelect').value=current;
}
function select(id,save=true){if(!byId.has(id))return;if(save&&id!==current){backstack.push(current);future.length=0;}current=id;detail();document.querySelectorAll('[data-node]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.node===id)));nodeEditor?.selectionChanged();}
const graph=document.querySelector('#graph'),svg=document.querySelector('#edges');
for(const n of nodes){const card=document.createElement('button');card.className='node '+n.status;card.dataset.node=n.id;card.type='button';card.onclick=()=>select(n.id);graph.append(card);}
for(const n of nodes)for(const id of n.deps){const edge=document.createElementNS('http://www.w3.org/2000/svg','path');edge.classList.add('edge');edge.dataset.from=id;edge.dataset.to=n.id;edge.innerHTML='<title>Manuscript reading path; not an audited Lean dependency.</title>';svg.append(edge);}
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
function renderEvidence(){
 const commit=escapeHTML(audit.upstream.commit),paperPath=audit.upstream.paperPath;
 document.querySelector('#evidenceContent').innerHTML=`<p class="notice">${text('论文已下载。对应 Fujita 最终定理的形式化源码尚未定位；本模块未进行 Lean 编译、精确类型核验或公理审计。','The manuscript is downloaded. The formalization of the corresponding final Fujita theorem has not been located; this module has no Lean build, exact-type check or axiom audit.')}</p><p>${text('已核查官方形式化清单、导入总表和未截断的代数几何、几何及 Comparator 目录。这不排除另一个仓库存在发布。','Checked the official formalization catalogue, import aggregator and complete AlgebraicGeometry, Geometry and Comparator directories. This does not rule out publication in another repository.')}</p><p>${text('源码查询日期','Source-check date')}: ${escapeHTML(audit.checkedAt)}<br>OpenAI math: <a href="https://github.com/openai/math/tree/${commit}" target="_blank" rel="noopener"><code>${commit}</code></a></p><p>${text('官方论文','Official manuscript')}: ${audit.manuscript.pages} ${text('页','pages')} · 2026-09-23<br>SHA-256: <code>${escapeHTML(audit.manuscript.sha256)}</code></p><div class="actions"><a class="button" href="paper.pdf" target="_blank" rel="noopener">PDF ↗</a><a class="button" href="paper.pdf" download>${text('下载论文','Download paper')} ↓</a><a class="button" href="fujita-release-snapshot.zip" download>${text('论文与发布元数据快照','Paper and release-metadata snapshot')} ↓</a><a class="button" href="audit.json">${text('模块状态数据','Module status data')} ↗</a><a class="button" href="verification.txt">${text('完整定位记录','Full discovery record')} ↗</a><a class="button" href="https://github.com/openai/math/blob/${commit}/${paperPath}" target="_blank" rel="noopener">${text('上游论文','Upstream manuscript')} ↗</a></div><h3>${text('待完成的导入与核验','Import and verification still needed')}</h3><ul>${audit.remaining.map(r=>`<li>${escapeHTML(r[english?1:0])}</li>`).join('')}</ul><p>${text('Disclosure：页面是文献阅读与发布材料导入记录。论文的数学正确性未在此独立验证；不据此宣称猜想已得到内核核验。','Disclosure: this page records manuscript reading and artifact import. The mathematical correctness of the paper has not been independently verified here; no kernel-verified resolution is claimed.')}</p>`;
}
renderEvidence();detail();
document.querySelector('#originalContent').innerHTML=statementPanel(root,english);
window.addEventListener('languagechange',()=>{document.querySelector('#originalContent').innerHTML=statementPanel(root,english);});
document.querySelector('#fullscreen').onclick=()=>document.fullscreenElement?document.exitFullscreen():document.documentElement.requestFullscreen();
document.querySelector('#expandGraph').onclick=()=>{document.body.classList.toggle('atlas-expanded');document.querySelector('#expandGraph').setAttribute('aria-pressed',String(document.body.classList.contains('atlas-expanded')));};
document.querySelector('[data-view="2d"]').onclick=()=>worlds.render();document.querySelector('[data-view="3d"]').hidden=true;
window.fujitaUI={worlds,nodeEditor,nodes,audit,selected:()=>current};
