// Present open geometry separately from verified deductions and theorem conditions.
const release = '20261003-formal-40';
const escapeHTML = value => String(value ?? '').replace(/[&<>"']/g, ch =>
  ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[ch]));

const gaps = {
  projectivesections: {
    zh: ['把射影坐标接到实际 Cartier 数据',
      '从闭嵌入 i:X→ℙⁿ_R，构造 A=i*𝒪(1) 的局部方程和坐标截面。',
      ['证明各坐标开集上的方程以局部环单位过渡。',
       '证明坐标截面有效，且它们的仿射非零集覆盖 X。']],
    en: ['Construct actual Cartier data from projective coordinates',
      'From i:X→ℙⁿ_R, construct local equations and coordinate sections for A=i*𝒪(1).',
      ['Prove that equations on coordinate charts differ by actual local-ring units.',
       'Prove that coordinate sections are effective and their affine nonvanishing loci cover X.']]
  },
  properformalfunctions: {
    zh: ['证明 proper 上同调核的统一消失',
      '∃c ∀n：ker[H¹(Iⁿ⁺꜀⁺¹𝒪_X)→H¹(𝒪_X)] 在向 H¹(Iⁿ⁺¹𝒪_X) 的转移下消失。',
      ['已证明：实际 Čech 上同调、模结构、两段正合性、障碍转移自然性及有限仿射覆盖。',
       '已证明：统一截面核界和实际非仿射比较单射。',
       '待证明：proper 分次上同调 Rees 模有限生成及统一消失界，去掉 hvanish，进而给出满射并去掉 hff。完整定理仍未完成。']],
    en: ['Prove uniform vanishing of the proper cohomology kernel',
      '∃c ∀n: ker[H¹(Iⁿ⁺꜀⁺¹O_X)→H¹(O_X)] vanishes under transition to H¹(Iⁿ⁺¹O_X).',
      ['Proved: actual Cech cohomology, module structure, two exactness statements, obstruction naturality and a finite affine cover.',
       'Proved: the uniform section-kernel bound and injectivity of the actual nonaffine comparison.',
       'Open: proper graded cohomology finite generation over Rees and uniform kernel vanishing. Remove hvanish, then prove surjectivity and remove hff. The complete theorem remains open.']]
  },
  chow: {
    zh: ['完成 Chow 构造的射影性',
      '按 Hartshorne 的有限仿射覆盖构造改造，证明复合态射是 projective。',
      ['接通有限覆盖中的射影嵌入与图像闭包。',
       '证明所需的相对射影性；仅证明 proper 还不足以完成此步。']],
    en: ['Finish projectivity in the Chow construction',
      'Use Hartshorne’s finite affine-cover construction to obtain a modification with projective composite.',
      ['Connect the projective embeddings from the finite cover with the graph closure.',
       'Prove relative projectivity; properness alone does not complete this step.']]
  }
};

const verifiedSteps = [
  ['actual_closed_cech_cohomology_exact', ['实际 Čech 一阶正合与障碍像已证明。', 'Actual first Cech exactness and the obstruction image are proved.']],
  ['actual_closed_cech_module_action', ['实际核上同调的全局函数模结构已证明。', 'The global-function module structure on actual kernel cohomology is proved.']],
  ['exists_actual_proper_affine_cech_cover', ['实际 proper 的有限仿射覆盖与仿射交集已构造。', 'A finite affine cover with affine intersections is constructed for the actual proper scheme.']],
  ['actual_relative_kernel_uniform_bound', ['实际 proper 限制的统一核界已证明。', 'The uniform kernel bound for actual proper restriction is proved.']],
  ['actual_relative_formal_functions_injective', ['实际非仿射形式函数比较映射单射已证明。', 'Injectivity of the actual nonaffine formal-functions comparison is proved.']],
  ['actual_relative_formal_functions_evaluation', ['真实非仿射相对比较映射及取值公式已构造。', 'The actual nonaffine relative comparison and evaluations are constructed.']],
  ['actual_closed_fiber_infinitesimal_nontrivial_idempotent', ['真实闭点纤维的相容非平凡幂等元已构造。', 'Compatible nontrivial idempotents from actual closed-point fibers are constructed.']],
  ['actual_closed_point_completion_local', ['真实闭点最大理想的完备环为局部环已证明。', 'The actual closed-point maximal-ideal completion is proved local.']],
  ['actual_fiber_closed_subset_dichotomy_of_closed_points', ['从闭点纤维推广到所有纤维的实际支撑二择一已证明。', 'Actual support dichotomy is proved to pass from closed-point fibers to all fibers.']],
  ['exists_effective_cartier_rational_twist', ['仿射底清分母：从给定 Cartier 数据构造有效 E。', 'Clear denominators over the affine base to construct effective E from supplied Cartier data.']],
  ['complete_integral_curve_ambient_cartier_principal_invariance', ['主除子移动保持实际完整曲线的交数。', 'Principal changes preserve actual complete-curve intersection.']],
  ['exists_effective_exceptional_covering_cartier_twist', ['给定严格负交数的 Cartier 除子时，构造 E 并证明 exceptional 素系数为正。', 'Given a strictly anti-positive Cartier divisor, construct E with positive exceptional-prime coefficients.']],
  ['complete_integral_curve_positive_of_affine_section_cover', ['给定实际仿射截面覆盖时，证明完整曲线交数严格为正。', 'Given an actual affine section cover, derive positive complete-curve intersection.']],
  ['proper_normal_birational_structure_sheaf_isIso', ['实际结构层 𝒪_Y→f_*𝒪_X 同构已证明。', 'The actual structure-sheaf isomorphism O_Y→f_*O_X is proved.']],
  ['actual_infinitesimal_nontrivial_idempotent', ['真实各阶加厚的相容非平凡幂等元已构造。', 'Compatible nontrivial idempotents on genuine thickenings are constructed.']],
  ['actual_affine_formal_functions_bijective', ['仿射源的规范完备化比较已证明；proper 非仿射比较仍缺。', 'The canonical affine-source completion comparison is proved; proper nonaffine comparison remains open.']],
  ['connected_complete_scheme_actual_crossing_curve', ['已连通的完整 Scheme 上，高维相交曲线的构造已完成。', 'Crossing curves are constructed in every dimension on already connected proper schemes.']],
  ['finiteType_perfectField_normalization_isFinite', ['实际正规化的有限性已证明。', 'Finiteness of actual normalization is proved.']],
  ['exists_embedded_complete_curve_real_projection_formula', ['实际 R-Cartier 曲线射影公式已证明。', 'The actual real-Cartier curve projection formula is proved.']],
  ['actual_relative_nef_canonical_pullback', ['实际相对 nef 的拉回保持已证明。', 'Preservation of actual relative nefness under pullback is proved.']]
];

export function buildInputProgress({node, openNodes, inputs, declarations = {}, english = false}) {
  const lang = english ? 'en' : 'zh';
  const text = (zh, en) => english ? en : zh;
  const hasCoordinateGap = openNodes.some(n => n.id === 'projectivesections');
  const relevant = new Set();
  if (hasCoordinateGap) for (const name of verifiedSteps.slice(0,4).map(s => s[0])) relevant.add(name);
  if (openNodes.some(n => n.id === 'properformalfunctions')) for (const name of ['actual_closed_cech_cohomology_exact','actual_closed_cech_module_action','exists_actual_proper_affine_cech_cover','actual_relative_kernel_uniform_bound','actual_relative_formal_functions_injective','actual_relative_formal_functions_evaluation','actual_closed_fiber_infinitesimal_nontrivial_idempotent','actual_closed_point_completion_local','actual_fiber_closed_subset_dichotomy_of_closed_points']) relevant.add(name);
  if (openNodes.some(n => n.id === 'chow')) for (const name of ['finiteType_perfectField_normalization_isFinite','exists_embedded_complete_curve_real_projection_formula','actual_relative_nef_canonical_pullback']) relevant.add(name);
  const proved = verifiedSteps.filter(([name]) => relevant.has(name) && declarations[name]);
  const explicitDone = inputs.filter(s => /^(已完成|已证明|Proved|Verified|Completed)\s*[:：]/i.test(s));
  const doneTexts = proved.length ? proved.map(([,labels]) => labels[english ? 1 : 0]) : explicitDone;
  if (!doneTexts.length && node.decl && declarations[node.decl]) doneTexts.push(text(
    `本节点的 Lean 声明已编译：${node.decl}。其适用条件及证明范围见上方说明。`,
    `This node’s Lean declaration is compiled: ${node.decl}. Its hypotheses and scope are stated above.`));
  const conditions = inputs.filter(s => !/^(已完成|已证明|待完成|尚缺|剩余|Proved|Verified|Completed|Remaining|Open)\s*[:：]/i.test(s));
  const gapCards = openNodes.map((n, i) => {
    const known = gaps[n.id]?.[lang];
    const title = known?.[0] || n.title;
    const goal = known?.[1] || text('此几何输入尚未证明；需要提供其实际 Lean 证明。', 'This geometric input still needs an actual Lean proof.');
    const todo = known?.[2] || (n.id === node.id ? inputs.filter(s => !explicitDone.includes(s)) : []);
    return `<article class="input-gap" data-input-gap="${escapeHTML(n.id)}"><div class="input-gap-title"><span class="input-gap-number">${i+1}</span><h4>${escapeHTML(title)}</h4><span class="input-gap-state">${text('未完成','OPEN')}</span></div><p>${escapeHTML(goal)}</p>${todo.length ? `<ul>${todo.map(s => `<li>${escapeHTML(s)}</li>`).join('')}</ul>` : ''}<button type="button" class="input-gap-link" data-select="${escapeHTML(n.id)}">${text('查看这项缺口 →','Inspect this gap →')}</button></article>`;
  }).join('');
  const isOpen = ['assumption','conditional','pending'].includes(node.status);
  const summary = openNodes.length ? text(`尚未形式化 · ${openNodes.length} 项具体缺口`, `Not yet formalized · ${openNodes.length} specific gap${openNodes.length===1?'':'s'}`) :
    node.status === 'pending' ? text('最终结论仍未接通', 'The final conclusion is still open') :
    text('此路径没有标记为未证明的几何输入', 'No unproved geometric input is marked on this path');
  const explanation = openNodes.length ? text('下面列的是仍须证明的几何环节，不包括通常的定理假设。', 'These are the geometric steps still requiring proof, separate from ordinary theorem conditions.') :
    node.status === 'pending' ? text('辅助定理通过不代表最终定理完成。还须完成实际几何实例化与结论的衔接。', 'Compiled helper theorems do not complete the final theorem. Actual geometric instantiation and the final deduction still need to be connected.') :
    text('这只说明图谱中没有开放输入；定理仍须满足其适用条件。', 'This concerns open inputs in the atlas; the theorem’s stated conditions still apply.');
  return `<section class="input-progress" data-input-progress="${escapeHTML(node.id)}"><div class="input-progress-heading"><span class="input-progress-icon ${openNodes.length ? 'open' : ''}">${openNodes.length?'?':'✓'}</span><div><h3>${escapeHTML(summary)}</h3><p>${escapeHTML(explanation)}</p></div></div><div class="input-progress-columns"><section class="input-pending-column"><h4 class="input-column-heading">? ${text('待证','Still to prove')}</h4>${gapCards || `<p class="input-small">${escapeHTML(explanation)}</p>`}</section>${doneTexts.length ? `<section class="input-completed"><h4 class="input-column-heading">✓ ${text('已证','Proved')}</h4><ul>${doneTexts.map(s => `<li>${escapeHTML(s)}</li>`).join('')}</ul><p class="input-small">${node.status === 'done' ? text('此节点在所列适用条件下已证明；完整主定理的剩余工作见独立目标卡。', 'This node is proved under its stated conditions; the separate main-target card lists the remaining work for the complete theorem.') : text('上述条件式结果不会自动证明其射影来源或完整 negativity lemma。', 'These conditional results do not automatically prove their projective origin or the complete negativity lemma.')}</p></section>` : `<section class="input-completed"><h4 class="input-column-heading">✓ ${text('已证','Proved')}</h4><p class="input-small">${text('此节点尚无已完成的 Lean 声明；下方前提的验证不等于本节点已证。','This node has no completed Lean declaration. Verified premises do not prove this node.')}</p></section>`}</div>${conditions.length ? `<details class="input-conditions"><summary>${text('定理的适用条件（不是完成进度）','Theorem conditions (not completion progress)')}</summary><ul>${conditions.map(s => `<li>${escapeHTML(s)}</li>`).join('')}</ul></details>` : ''}${isOpen && openNodes.length ? `<p class="input-color-note"><span aria-hidden="true">?</span>${text('黄色问号＝此项尚未证明。含此输入的结论目前只完成条件式验证。', 'Yellow question mark = this item is unproved. Results using it are currently verified only conditionally.')}</p>` : ''}</section>`;
}

export async function installInputProgress() {
  const root = document.querySelector('#overviewPanel');
  if (!root) return;
  const appScript = document.querySelector('script[src*="app.js"]');
  const proof = appScript ? new URL(appScript.src).searchParams.get('proof') : '';
  const moduleURL = new URL('./graph-data.js', import.meta.url);
  moduleURL.searchParams.set('v', release);
  if (proof) moduleURL.searchParams.set('proof', proof);
  const {nodes} = await import(moduleURL.href);
  const byId = new Map(nodes.map(n => [n.id,n]));
  const sheet = document.createElement('link');
  sheet.rel = 'stylesheet';sheet.href = new URL(`./input-progress.css?v=${release}`, import.meta.url).href;
  document.head.append(sheet);
  installInspectorActions();
  let declarations = {}, saved = null, queued = false;
  const observer = new MutationObserver(() => {
    if (queued) return;queued=true;
    queueMicrotask(() => {queued=false;refresh();});
  });
  const watch = () => observer.observe(root,{childList:true,subtree:true,characterData:true});
  function refresh(force=false) {
    const id = location.hash.startsWith('#node=') ? location.hash.slice(6) : 'proper';
    const node = byId.get(id);if (!node) return;
    const english = document.documentElement.lang.startsWith('en');
    const old = root.querySelector('[data-input-progress]');
    if (old && !force) return;
    const removed = [];
    let inputs = [];
    if (!old) {
      const headers = [...root.querySelectorAll(':scope > h3')];
      const inputHeader = headers.find(h => /^(尚需建立的几何内容|当前输入\s*\/\s*假设|Remaining geometric inputs|Current inputs\s*\/\s*hypotheses)$/.test(h.textContent.trim()));
      if (!inputHeader) return;
      const inputList = inputHeader.nextElementSibling;
      if (inputList?.tagName === 'UL') inputs=[...inputList.children].map(li => li.textContent.trim());
      removed.push(inputHeader,inputList);
      const pathHeader = headers.find(h => /^(沿这条路径|Assumed geometric inputs on this path)/.test(h.textContent.trim()));
      if (pathHeader) {
        let sibling=pathHeader.nextElementSibling;
        removed.push(pathHeader);
        while(sibling && sibling.tagName!=='H3') {const next=sibling.nextElementSibling;removed.push(sibling);sibling=next;}
      } else {
        const empty=[...root.querySelectorAll(':scope > .empty')].find(e=>/此依赖链|This path has no/.test(e.textContent));
        if(empty) removed.push(empty);
      }
      saved={id,english,inputs};
    } else if(saved?.id===id && saved.english===english) inputs=saved.inputs;
    else return;
    const seen=new Set();
    const visit=nid=>{if(seen.has(nid))return;seen.add(nid);(byId.get(nid)?.deps||[]).forEach(visit);};
    visit(id);
    const openNodes=[...seen].map(nid=>byId.get(nid)).filter(n=>n?.status==='assumption');
    observer.disconnect();
    if(old) old.remove();
    removed.filter(Boolean).forEach(el=>el.remove());
    root.insertAdjacentHTML('afterbegin', buildInputProgress({node,openNodes,inputs,declarations,english}));
    watch();
  }
  watch();refresh();
  const snapshotURL=new URL('./snapshot.json',import.meta.url);
  snapshotURL.searchParams.set('v',proof || release);
  try {const response=await fetch(snapshotURL);if(response.ok){declarations=(await response.json()).declarations||{};refresh(true);}}
  catch { /* The main evidence panel owns snapshot failure reporting. */ }
}

function installInspectorActions() {
  const header=document.querySelector('#detailHeader');
  const steps=document.querySelector('#stepsPanel'), source=document.querySelector('#sourcePanel');
  if(!header || !steps || !source || document.querySelector('#inputDetailDialog'))return;
  document.querySelector('.detail-tabs')?.setAttribute('hidden','');
  document.querySelector('#overviewTab')?.click();
  const dialog=document.createElement('dialog');dialog.id='inputDetailDialog';dialog.className='input-detail-dialog';
  dialog.innerHTML='<div class="input-dialog-toolbar"><h2 id="inputDialogTitle"></h2><button type="button" class="input-dialog-close" aria-label="Close">×</button></div><div class="input-dialog-content"></div>';
  document.body.append(dialog);
  dialog.querySelector('.input-dialog-content').append(steps,source);
  dialog.querySelector('.input-dialog-close').onclick=()=>dialog.close();
  dialog.addEventListener('click',e=>{if(e.target===dialog){const r=dialog.getBoundingClientRect();if(e.clientX<r.left||e.clientX>r.right||e.clientY<r.top||e.clientY>r.bottom)dialog.close();}});
  const update=()=>{
    if(header.querySelector('.input-inspector-actions'))return;
    const en=document.documentElement.lang.startsWith('en');
    const actions=document.createElement('div');actions.className='input-inspector-actions';
    actions.innerHTML=`<span class="input-goal-label">${en?'PROOF GOAL':'要证明'}</span><button type="button" data-inspector-action="source" title="${en?'Open Lean source':'打开 Lean 源码'}">Lean</button><button type="button" data-inspector-action="steps" title="${en?'Open proof steps':'打开证明步骤'}">Proof</button>`;
    header.prepend(actions);
    const statement=header.querySelector('.statement');
    const status=header.querySelector(':scope > .pill');
    if(statement && status)statement.insertAdjacentElement('afterend',status);
    const extra=[...header.querySelectorAll(':scope > p:not(.statement)')];
    if(extra.length){
      const explanation=document.createElement('details');explanation.className='input-scope-details';
      const summary=document.createElement('summary');summary.textContent=en?'Proof scope and conditions':'证明范围与条件';
      explanation.append(summary,...extra);header.append(explanation);
    }
    actions.onclick=e=>{
      const button=e.target.closest('[data-inspector-action]');if(!button)return;
      const isSource=button.dataset.inspectorAction==='source';source.hidden=!isSource;steps.hidden=isSource;
      document.querySelector('#inputDialogTitle').textContent=(isSource?(en?'Lean source':'Lean 源码'):(en?'Proof steps':'证明步骤'))+' · '+header.querySelector('h2').textContent;
      dialog.querySelector('.input-dialog-close').setAttribute('aria-label',en?'Close dialog':'关闭弹窗');
      dialog.showModal();dialog.querySelector('.input-dialog-content').scrollTop=0;
    };
  };
  new MutationObserver(update).observe(header,{childList:true,subtree:true});update();
}

if(typeof document!=='undefined')installInputProgress().catch(error=>console.error('Input progress panel:',error));
