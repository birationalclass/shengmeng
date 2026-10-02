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
    <p>${english ? 'The chosen route defines degree directly by Cartier local orders on the normalization. The displayed global projection equalities below remain goals.' : '采用的路线是在正规化上直接求 Cartier 局部阶数。下方显示的全局投影等式仍是待证明目标。'}</p>
    <div class="formula">(π<sup>*</sup>D) · Γ = deg(h<sup>*</sup>L)</div>
    <div class="formula">D · π<sub>*</sub>[Γ] = [k(Γ):k(C)] deg(L)</div>
    <ol class="curve-proof-stages">
      <li class="curve-stage-done"><span>✓</span><div><b>${english ? 'Pullback around the square: verified' : '交换图的拉回同构：已验证'}</b><p>${english ? 'Actual Scheme modules; only the commutativity of the square is required.' : '使用真实 Scheme 模层，只要求上面的交换关系。'}</p><button class="text-button" data-select="pullbackdiagram">${english ? 'Read the Lean proof →' : '查看 Lean 证明 →'}</button></div></li>
      <li class="curve-stage-done"><span>✓</span><div><b>${english ? 'Point divisors and multiplicity: verified' : '点除子与重数计数：已验证'}</b><p>m<sub>q</sub> = length(𝒪<sub>Γ,q</sub> ⊗<sub>𝒪<sub>C,p</sub></sub> k(p))<br>Σ m<sub>q</sub>[k(q):k] = r[k(p):k].</p><button class="text-button" data-select="pointtensor">${english ? 'Point pullback and counting proof →' : '点拉回与计数证明 →'}</button></div></li>
      <li class="curve-stage-done"><span>✓</span><div><b>${english ? 'Finite signed divisors: verified' : '有限带符号除子：已验证'}</b><div class="formula">deg(h<sup>*</sup>D) = [L:K] deg(D)</div><p>${english ? 'Actual tensor lengths extend by additivity. Principal pullback, support and effectivity are proved. Over an algebraically closed field the multiplicity sum is [L:K], including inseparable degree.' : '实际张量长度经可加性延伸；主除子拉回、支撑及有效性已证明。代数闭域下重数总和为 [L:K]，包含不可分次数。'}</p><button class="text-button" data-select="affinedivisor">${english ? 'Read the finite-divisor proof →' : '查看有限除子的证明 →'}</button></div></li>
      <li class="curve-stage-done"><span>✓</span><div><b>${english ? 'Norm/valuation product formula: verified' : '范数／赋值乘积公式：已验证'}</b><p>${english ? 'Actual integral closures, their finiteness, normalized infinity orders and norm/divisor identities are constructed in arbitrary characteristic with a separable parameter. Identifying these places and residue weights with a supplied complete Scheme curve remains open.' : '任意特征下，以可分参数构造实际整闭包、有限性、归一化无穷远阶数及范数主除子等式。这些赋值点及剩余域权重与给定完整 Scheme 曲线的识别仍待完成。'}</p><button class="text-button" data-select="functionproduct">${english ? 'Read the norm/valuation proof →' : '查看范数／赋值证明 →'}</button></div></li>
      <li class="curve-stage-done"><span>✓</span><div><b>${english ? 'Actual Cartier restriction and moving: verified' : '真实 Cartier 限制与移动：已验证'}</b><p>${english ? 'Use actual generic stalk units without assuming dominance. Effective restrictions have nonnegative order sum, positive on meeting support. Principal moving constructs restriction even for a curve in the original support. Degree independence under this move is still open.' : '使用真实泛点 stalk 单位，不假定 dominant。有效限制阶数和非负，相交则严格正。主除子移动为原来包含在支撑中的曲线也构造限制；移动后的次数与选择无关仍待证明。'}</p><button class="text-button" data-select="cartiercurve">${english ? 'Read the Cartier-order proof →' : '查看 Cartier 阶数证明 →'}</button></div></li>
      <li class="curve-stage-open"><span>○</span><div><b>${english ? 'Global Cartier-order projection: still open' : '全局 Cartier 阶数投影：尚待完成'}</b><div class="formula">deg(h<sup>*</sup>D) = [k(Γ):k(C)] deg(D)</div><p>${english ? 'Connect actual complete-curve closed points to the constructed valuation places, prove principal-move and presentation-independent degree, and globalize the proved finite-divisor formula. Normalization and the point-image zero case also remain open. A general line-bundle degree API is no longer a prerequisite of the selected route.' : '接通实际完整曲线闭点与构造的赋值点，证明主除子移动及表示无关，再将已证明的有限除子公式全局化。正规化与像为点的零次数也待接通。所选路线不再要求先建立任意线丛的全部次数接口。'}</p></div></li>
    </ol>
  </section>`;
}
