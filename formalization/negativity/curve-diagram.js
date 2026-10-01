// This is a mathematical commutative square, independent of the graph camera.
export function curveDiagramPanel(node, english) {
  if (!['projection', 'pullbackdiagram'].includes(node.id)) return '';
  const title = english ? 'Restrict to the curve: the commutative square' : '限制到曲线：交换图';
  const label = english ? 'Γ maps into X′; C maps into X; h and π make the square commute.' : 'Γ 嵌入 X′，像曲线 C 嵌入 X；h 与 π 构成交换图。';
  return `<section class="curve-diagram-panel">
    <h3>${title}</h3>
    <p>${english ? 'For a curve image C=π(Γ), h=π|Γ and π∘i=j∘h.' : '当 C=π(Γ) 是曲线时，h=π|Γ，且 π∘i=j∘h。'}</p>
    <svg class="curve-square" viewBox="0 0 320 165" role="img" aria-label="${label}">
      <defs><marker id="curve-square-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="currentColor"/></marker></defs>
      <g fill="none" stroke="currentColor" stroke-width="1.5" marker-end="url(#curve-square-arrow)">
        <path d="M 67 30 H 253"/><path d="M 67 139 H 253"/>
        <path d="M 43 52 V 115"/><path d="M 278 52 V 115"/>
      </g>
      <g fill="currentColor" text-anchor="middle" class="curve-square-objects"><text x="43" y="38">Γ</text><text x="278" y="38">X′</text><text x="43" y="147">C</text><text x="278" y="147">X</text></g>
      <g fill="currentColor" text-anchor="middle" class="curve-square-maps"><text x="160" y="22">i</text><text x="160" y="130">j</text><text x="24" y="88">h</text><text x="299" y="88">π</text></g>
    </svg>
    <div class="formula">i<sup>*</sup>π<sup>*</sup>𝒪<sub>X</sub>(D) ≅ h<sup>*</sup>j<sup>*</sup>𝒪<sub>X</sub>(D)</div>
    <p>${english ? 'Intersection is the degree after restriction to the curve. Put L=j*𝒪_X(D).' : '交数是限制到曲线后取次数。令 L=j*𝒪_X(D)。'}</p>
    <div class="formula">(π<sup>*</sup>D) · Γ = deg(h<sup>*</sup>L)</div>
    <div class="formula">D · π<sub>*</sub>[Γ] = [k(Γ):k(C)] deg(L)</div>
    <ol class="curve-proof-stages">
      <li class="curve-stage-done"><span>✓</span><div><b>${english ? 'Pullback around the square: verified' : '交换图的拉回同构：已验证'}</b><p>${english ? 'Actual Scheme modules; only the commutativity of the square is required.' : '使用真实 Scheme 模层，只要求上面的交换关系。'}</p><button class="text-button" data-select="pullbackdiagram">${english ? 'Read the Lean proof →' : '查看 Lean 证明 →'}</button></div></li>
      <li class="curve-stage-done"><span>✓</span><div><b>${english ? 'Point divisors and multiplicity: verified' : '点除子与重数计数：已验证'}</b><p>m<sub>q</sub> = length(𝒪<sub>Γ,q</sub> ⊗<sub>𝒪<sub>C,p</sub></sub> k(p))<br>Σ m<sub>q</sub>[k(q):k] = r[k(p):k].</p><button class="text-button" data-select="pointtensor">${english ? 'Point pullback and counting proof →' : '点拉回与计数证明 →'}</button></div></li>
      <li class="curve-stage-open"><span>○</span><div><b>${english ? 'Global line-bundle degree: still open' : '全局线丛次数公式：尚待完成'}</b><div class="formula">deg(h<sup>*</sup>L) = [k(Γ):k(C)] deg(L)</div><p>${english ? 'Extend from point divisors by additivity and glue on complete curves; also connect normalization and the point-image case to actual degree. The square alone does not prove this last equality.' : '先由点除子可加性延伸，再在完整曲线上拼接，并接入正规化及像为点的次数计算。交换图本身还不能推出最后这条等式。'}</p></div></li>
    </ol>
  </section>`;
}
