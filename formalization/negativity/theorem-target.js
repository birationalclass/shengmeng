import {statementPanel,escapeHTML,declarationKind,emblem,graphStatement} from './theorem-statements.js?v=20261004-explain-47';
import {english} from './i18n.js?v=20261004-explain-47';

// The module's final mathematical target is separate from the proof-step DAG.
// Its status must not inherit the status of any compiled auxiliary lemma.
const math = (content, label, display = false) =>
  `<math xmlns="http://www.w3.org/1998/Math/MathML"${display ? ' display="block"' : ''} aria-label="${label}">${content}</math>`;
const k = math('<mi>k</mi>', 'k');
const f = math('<mi>f</mi><mo>:</mo><mi>X</mi><mo>→</mo><mi>Y</mi>', 'f: X → Y');
const D = math('<mi>D</mi>', 'D');
const minusD = math('<mo>−</mo><mi>D</mi>', '−D');
const effective = math('<mi>D</mi><mo>≥</mo><mn>0</mn>', 'D ≥ 0');
const y = math('<mi>y</mi><mo>∈</mo><mi>Y</mi>', 'y ∈ Y');
const rCartier = `${math('<mi mathvariant="normal">ℝ</mi>', 'ℝ')}-Cartier`;
const fNef = `${math('<mi>f</mi>', 'f')}-nef`;
const fiber = '<msup><mi>f</mi><mrow><mo>−</mo><mn>1</mn></mrow></msup><mo>(</mo><mi>y</mi><mo>)</mo>';
const support = '<mi mathvariant="normal">Supp</mi><mspace width="0.15em"/><mi>D</mi>';
const equivalence = math(
  '<mi>D</mi><mo>≥</mo><mn>0</mn><mspace width="0.8em"/><mo>⟺</mo><mspace width="0.8em"/><msub><mi>f</mi><mo>∗</mo></msub><mi>D</mi><mo>≥</mo><mn>0</mn>',
  'D ≥ 0 if and only if f_*D ≥ 0', true);
const disjoint = math(`${fiber}<mo>∩</mo>${support}<mo>=</mo><mi mathvariant="normal">∅</mi>`,
  'f⁻¹(y) ∩ Supp D = ∅');
const contained = math(`${fiber}<mo>⊆</mo>${support}`,
  'f⁻¹(y) ⊆ Supp D');

function createTheoremCard(view) {
  let targetNode=null;
  const card = document.createElement('section');
  card.id = `theoremTarget-${view}`;
  card.className = 'theorem-target-card';
  card.dataset.theoremCard = view;
  card.dataset.conclusionOne = 'done';
  card.dataset.conclusionTwo = 'done';
  card.style.setProperty('--theorem-unit', '1');
  card.setAttribute('aria-labelledby', `theoremTargetTitle-${view}`);
  function finishCompactCard(expanded){
    card.dataset.expanded=String(expanded);
    const summary=document.createElement('div');summary.className='theorem-target-summary node-proposition';summary.hidden=expanded;
    summary.innerHTML=graphStatement(targetNode||{id:'proper'},english);
    if(!targetNode||targetNode.id==='proper')summary.querySelector('.graph-conclusion span').innerHTML=equivalence+'<br>'+ (english?'If D is effective, each fiber avoids Supp D or lies in it.':'D 有效时，每个纤维与 Supp D 不交或包含于 Supp D。');
    card.querySelector('.theorem-target-body').before(summary);
    for(const side of ['top','bottom','left','right']){const port=document.createElement('span');port.className='theorem-port';port.dataset.side=side;port.setAttribute('aria-hidden','true');card.append(port);}
    card.querySelector('.theorem-target-toggle').addEventListener('click',()=>{const open=card.querySelector('.theorem-target-toggle').getAttribute('aria-expanded')==='true';summary.hidden=open;card.dataset.expanded=String(open);});
  }
  function renderLanguage(){
  const expanded=card.querySelector('.theorem-target-toggle')?.getAttribute('aria-expanded')==='true';
  const conventionsOpen=card.querySelector('.theorem-target-conventions')?.open||false;
  if(targetNode&&targetNode.id!=='proper'){
    const verified=['done','conditional'].includes(targetNode.status),status=verified?(english?'✓ Lean verified':'✓ Lean 已验证'):(english?'Open proof':'待补证明');
    card.dataset.targetNode=targetNode.id;card.dataset.targetStatus=targetNode.status;
    card.innerHTML=`<header class="theorem-target-heading"><div class="theorem-target-title"><span class="theorem-target-label">${english?'MAIN TARGET OF THIS WORLD':'当前世界的主目标'}</span><h2 id="theoremTargetTitle-${view}">${escapeHTML(targetNode.title)}</h2></div><span class="theorem-target-status">${status}${declarationKind(targetNode)==='definition'?' · '+(english?'Construction':'定义 / 构造'):''}</span><nav class="theorem-target-actions"><button type="button" class="button small" data-select="${targetNode.id}">${english?'Lean & proof':'Lean 与证明'}</button><button type="button" class="button small theorem-target-toggle" aria-expanded="${expanded}">${expanded?(english?'Collapse':'收起'):(english?'Expand':'展开')}</button></nav></header><div class="theorem-target-body" ${expanded?'':'hidden'}>${statementPanel(targetNode,english)}</div>`;
    const body=card.querySelector('.theorem-target-body'),toggle=card.querySelector('.theorem-target-toggle');toggle.onclick=()=>{const open=toggle.getAttribute('aria-expanded')!=='true';toggle.setAttribute('aria-expanded',String(open));toggle.textContent=open?(english?'Collapse':'收起'):(english?'Expand':'展开');body.hidden=!open;card.dispatchEvent(new Event('theoremcardchange'));};
    finishCompactCard(expanded);return;
  }
  card.dataset.targetNode='proper';card.dataset.targetStatus='done';
  const text = english ? {
    label: 'FINAL THEOREM · THEOREM 1.4',
    title: 'Negativity lemma',
    status: '✓ Complete theorem verified by Lean',
    goal: 'Proof dependencies →',
    original: 'Original theorem ↗',
    collapse: 'Collapse', expand: 'Expand theorem',
    hypotheses: `Let ${k} be an algebraically closed field of arbitrary characteristic, and let ${f} be a proper birational morphism of normal ${k}-varieties (integral, separated and of finite type). Let ${D} be an ${rCartier} divisor on ${math('<mi>X</mi>', 'X')} such that ${minusD} is ${fNef}.`,
    first: 'Effectivity · ✓ Verified by Lean',
    second: 'Fiber support · ✓ Verified by Lean',
    condition: `If ${effective}, then for every ${y},`,
    or: 'or',
    note: 'One module, one final theorem. The cards below are its proof steps and inputs.',
    definitions: 'Conventions',
    conventions: `Effectivity and support refer to prime-divisor coefficients. The pushforward is the Weil-divisor pushforward. The ${fNef} condition is tested on complete integral curves contracted by ${math('<mi>f</mi>', 'f')}; intersection numbers use line-bundle degree on the normalization. Fibers and support containments are set-theoretic. Both conclusions belong to this one theorem.`,
  } : {
    label: '最终定理 · 原稿 THEOREM 1.4',
    title: 'Negativity lemma',
    status: '✓ 完整定理已通过 Lean',
    goal: '查看证明依赖 →',
    original: '原稿定理 ↗',
    collapse: '收起', expand: '展开定理',
    hypotheses: `设 ${k} 为任意特征的代数闭域，${f} 为正规 ${k}-簇（整、分离、有限型）之间的 proper 双有理态射。设 ${D} 为 ${math('<mi>X</mi>', 'X')} 上的 ${rCartier} 除子，且 ${minusD} 为 ${fNef}。`,
    first: '有效性 · ✓ 已通过 Lean',
    second: '纤维与支撑 · ✓ 已通过 Lean',
    condition: `若 ${effective}，则对每个 ${y}，`,
    or: '或',
    note: '一个模块，一个最终定理。下方卡片是它的证明步骤与输入。',
    definitions: '符号与约定',
    conventions: `有效性与支撑按素除子系数理解；推出为 Weil 除子的推出。${fNef} 只在被 ${math('<mi>f</mi>', 'f')} 压缩的完整整曲线上检验，交数在曲线正规化上取线丛次数。纤维与支撑的包含按集合意义理解。两条结论属于同一个定理。`,
  };
  card.innerHTML = `
    <header class="theorem-target-heading">
      <div class="theorem-target-title"><span class="theorem-target-label">${text.label}</span><h2 id="theoremTargetTitle-${view}">${text.title}</h2></div>
      <span class="theorem-target-status">${text.status}</span>
      <nav class="theorem-target-actions" aria-label="${english ? 'Theorem actions' : '定理操作'}">
        <button type="button" class="button small" data-select="proper">${text.goal}</button>
        <a class="button small" href="#paper-proper">${text.original}</a>
        <button type="button" class="button small theorem-target-toggle" aria-expanded="true" aria-controls="theoremTargetBody-${view}">${text.collapse}</button>
      </nav>
    </header>
    <div id="theoremTargetBody-${view}" class="theorem-target-body">
      <h3 class="statement-part-label">${emblem('let')}${english?'Let · Conditions':'设 · 条件'}</h3><p class="theorem-target-hypotheses">${text.hypotheses}</p>
      <h3 class="statement-part-label">${emblem('then')}${english?'Then · Conclusion':'则 · 结论'}</h3><div class="theorem-target-conclusions">
        <div class="theorem-target-conclusion"><h3><span>(1)</span> ${text.first}</h3>${equivalence}</div>
        <div class="theorem-target-conclusion"><h3><span>(2)</span> ${text.second}</h3><p>${text.condition}</p><div class="theorem-target-fiber">${disjoint}<span>${text.or}</span>${contained}<span>.</span></div></div>
      </div>
      <div class="theorem-target-footnote"><p>${text.note}</p><details class="theorem-target-conventions"><summary>${text.definitions}</summary><p>${text.conventions}</p></details></div>
    </div>`;
  const toggle = card.querySelector('.theorem-target-toggle');
  const body = card.querySelector('.theorem-target-body');
  toggle.setAttribute('aria-expanded',String(expanded));toggle.textContent=expanded?text.collapse:text.expand;body.hidden=!expanded;
  card.querySelector('details').open=conventionsOpen;
  const changed = () => card.dispatchEvent(new Event('theoremcardchange'));
  toggle.addEventListener('click', () => {
    const expanded = toggle.getAttribute('aria-expanded') !== 'true';
    toggle.setAttribute('aria-expanded', String(expanded));
    toggle.textContent = expanded ? text.collapse : text.expand;
    body.hidden = !expanded;
    changed();
  });
  card.querySelector('details').addEventListener('toggle', changed);
  finishCompactCard(expanded);
  }
  renderLanguage();
  window.addEventListener('languagechange',()=>{renderLanguage();card.dispatchEvent(new Event('theoremcardchange'));});
  return {
    element: card,
    setTarget(node){if(targetNode?.id!==node?.id)card.querySelector('.theorem-target-toggle')?.setAttribute('aria-expanded','false');targetNode=node;renderLanguage();card.dispatchEvent(new Event('theoremcardchange'));},
    layout(proofLayout, factor = 1, nodeFactor = factor) {
      const points = [...proofLayout.values()];
      const left = Math.min(...points.map(p => p.x));
      const right = Math.max(...points.map(p => p.x + 300 * nodeFactor));
      const top = Math.min(...points.map(p => p.y));
      const unit = parseFloat(card.style.getPropertyValue('--theorem-unit')) || 1;
      const w = 420 * factor, h = card.offsetHeight / unit * factor;
      const bottom=Math.max(...points.map(p=>p.y+(p.visibleH||p.h)));
      return {x:right+70*factor, y:(top+bottom-h)/2, w, h};
    },
    place(x, y, unit, z = 3) {
      card.style.setProperty('--theorem-unit', String(unit));
      card.style.left = Math.round(x) + 'px';
      card.style.top = Math.round(y) + 'px';
      card.style.zIndex = String(z);
    },
  };
}

export function installTheoremTarget() {
  // One theorem, rendered as a world-space card in each camera view.
  return {createCard: createTheoremCard};
}
