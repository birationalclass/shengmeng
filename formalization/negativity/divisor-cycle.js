export function divisorCyclePanel(n, en) {
 if(n.id!=='strict')return '';
 return `<section class="proof-formula">
 <h3>${en?'What “cycle” means here':'这里的 cycle 是什么'}</h3>
 <p>${en?'It is the divisor written as a finite formal sum of prime divisors, with its actual coefficients.':'就是将除子写成素除子的有限形式和，保留其实际系数。'}</p>
 <div class="formula">D = Σ<sub>P</sub> a<sub>P</sub>[P]</div>
 <h3>${en?'The precise codimension-one fact':'具体需要的余维一性质'}</h3>
 <p>${en?'For proper birational f:X→Y with normal target, f is an isomorphism over a neighborhood of the generic point of each prime divisor Q⊂Y. There is a unique strict transform Q̃ and its function field is k(Q).':'f:X→Y 为 proper birational，Y 正规。对每个素除子 Q⊂Y，f 在 Q 的泛点附近是同构；因此存在唯一严格变换 Q̃，且其函数域为 k(Q)。'}</p>
 <div class="formula">f<sub>*</sub>[Q̃] = [Q]</div>
 <p>${en?'If a prime divisor P is contracted to codimension at least two, its divisor pushforward is zero.':'若素除子 P 被压缩到余维至少 2，则它在除子推出中贡献为零。'}</p>
 <div class="formula">f<sub>*</sub>[P] = 0 &nbsp; (P exceptional)</div>
 <h3>${en?'The coefficient identity actually used':'证明实际使用的系数等式'}</h3>
 <div class="formula">coeff<sub>Q</sub>(f<sub>*</sub>D) = coeff<sub>Q̃</sub>(D)</div>
 <p>${en?'Thus f_*D≥0 forces every negative coefficient of D to lie on an exceptional divisor. The coefficient-model implication is verified; the actual codimension-one open and corresponding stalks are now verified. The strict injection, geometric exceptional indices and actual pushforward coefficient identity are verified. Actual Cartier coefficients and real Cartier push-pull are verified separately.':'所以 f_*D≥0 时，D 的负系数分量必为 exceptional。系数模型上的这一推导已验证；实际余维一同构开集与对应 stalk 已验证；实际 strict 单射、几何 exceptional 指标及 cycle 推出系数已接通；实际 Cartier 系数和 R-Cartier 推拉也已单独验证。'}</p>
 <button class="text-button" data-select="negative">${en?'Verified coefficient implication →':'已验证的系数推导 →'}</button>
 <p><a href="https://stacks.math.columbia.edu/tag/0BFP" target="_blank" rel="noopener">Stacks · 33.17.3 ↗</a></p>
 </section>`;
}
