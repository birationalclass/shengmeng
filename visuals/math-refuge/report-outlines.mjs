// Bilingual seminar summaries, adapted from the two CC BY 4.0 preprints.
// These are concise boards, not a transcript or an assertion of a live event.
const page=(source,title,tex,text,titleEn,textEn)=>({source,title,tex,text,en:{source,title:titleEn,text:textEn}});
export const reportOutlines={
  ye:[
    {kind:'cover',source:'报告',title:'格点上的渐近最优 Hardy–Rellich 不等式',author:'叶东',tex:'',text:'与 Xia Huang 合作\narXiv:2607.23057',en:{source:'SEMINAR',title:'Asymptotically sharp Hardy–Rellich inequalities on lattices',author:'Dong Ye',text:'Joint work with Xia Huang\narXiv:2607.23057'}},
    page('§ 1 · (1.4)','离散最佳常数',String.raw`\sum_{n\in\mathbb Z^d}|\mathcal D^m u(n)|^2\geq\mathcal C_{m,d}\sum_{n\ne0}\frac{|u(n)|^2}{|n|^{2m}}`,
      '取有限支撑且在原点为零的实函数。偶数阶使用离散 Laplace 算子的幂；奇数阶再取一次离散梯度。',
      'The discrete optimal constant','Use finitely supported real functions vanishing at the origin. Even orders use powers of the discrete Laplacian; odd orders add a discrete gradient.'),
    page('定理 1.1','固定阶数的高维极限',String.raw`\lim_{d\to\infty}\frac{\mathcal C_{m,d}}{d^m}=2^m\qquad(m\geq1\ \text{fixed})`,
      '先固定阶数，再令维数趋于无穷。该极限给出最佳常数的渐近首项。',
      'The high-dimensional limit','Fix the order before taking the dimension to infinity. The limit identifies the leading asymptotic coefficient.'),
    page('引理 1.2','Fourier 转化',String.raw`\begin{gathered}\sum_{n\ne0}\frac{|u(n)|^2}{|n|^{2m}}=\int_{\mathbb T^d}|D^m\Psi|^2\\\sum_n|\mathcal D^m u(n)|^2=4^m\int_{\mathbb T^d}|D^{2m}\Psi|^2\omega^m\end{gathered}`,
      '存在零均值光滑周期函数 Ψ，将格点问题转化为平坦环面上的加权估计。',
      'Fourier reduction','A smooth periodic function Ψ with zero mean converts the lattice problem into weighted estimates on a flat torus.'),
    page('§ 2','权函数与集中估计',String.raw`\begin{gathered}\omega(x)=\sum_{j=1}^d\sin^2(x_j/2)\\\rho=\frac{2\omega}{d}=\frac1d\sum_{j=1}^d(1-\cos x_j)\end{gathered}`,
      '在均匀概率测度下，归一化权函数是独立同分布随机变量的均值。集中与熵估计控制退化区域。',
      'Weights and concentration','Under uniform probability measure, the normalized weight is an average of independent variables. Concentration and entropy estimates control degeneracy.'),
    page('定理 1.3','环面上的渐近常数',String.raw`\lim_{d\to\infty}\frac{C_{d,k,\ell,\gamma}}{d^{k-\ell}}=2^{\ell-k}`,
      '固定非负整数 k、ℓ 与正整数 γ，满足 0＜k−ℓ≤γ。加权 Hardy–Rellich 估计经迭代给出格点结论。',
      'Asymptotic torus constants','Fix nonnegative integers k, ℓ and a positive integer γ with 0 < k − ℓ ≤ γ. Iteration of weighted estimates yields the lattice result.')
  ],
  hu:[
    {kind:'cover',source:'报告',title:'一般型 Gorenstein 极小三维簇的典范映射次数',author:'胡勇',tex:'',text:'与 Jiabin Du 合作\narXiv:2606.31170',en:{source:'SEMINAR',title:'On the canonical degree of a Gorenstein minimal threefold of general type',author:'Yong Hu',text:'Joint work with Jiabin Du\narXiv:2606.31170'}},
    page('§ 1','几何设定',String.raw`\begin{gathered}\phi_X:X\dashrightarrow\Sigma\subset\mathbb P^{p_g(X)-1}\\d=\deg(\phi_X),\qquad p_g(X)=h^0(X,K_X)\end{gathered}`,
      '在复数域上，取一般型 Gorenstein 极小射影三维簇，并假设典范映射到其像是泛有限的。',
      'Geometric setup','Work over the complex numbers with a projective Gorenstein minimal threefold of general type and a generically finite canonical map.'),
    page('定理 1.2','典范次数的上界',String.raw`p_g(X)>243\quad\Longrightarrow\quad\deg(\phi_X)\leq72`,
      '沿用前述几何假设。几何亏格足够大时，典范映射次数受到更强的限制。',
      'Bounding the canonical degree','Under the preceding geometric hypotheses, sufficiently large geometric genus gives the stronger degree bound.'),
    page('定理 1.2','等号的必要条件',String.raw`\begin{gathered}d=72\ \Longrightarrow\ p_g(F)=3,\quad q(F)=0\\K_F^2=36,\qquad\deg(\phi_F)=36\end{gathered}`,
      '仍假设 p_g(X)＞243。此时一般 Albanese 纤维 F 必须是光滑的一般型极小曲面。这里给出的是等号成立的必要条件。',
      'Necessary conditions for equality','Still assume p_g(X) > 243. The general Albanese fibre F must be a smooth minimal surface of general type. These are necessary conditions.'),
    page('推论 1.4','高次数与正则纤维',String.raw`p_g(X)>243,\quad d>64\quad\Longrightarrow\quad\dim F=2,\quad q(F)=0`,
      '在定理的同一组假设下，一般 Albanese 纤维为不规则度等于零的曲面。',
      'High degree and regular fibres','With the theorem’s hypotheses, the general Albanese fibre is a surface of irregularity zero.'),
    page('§ 3 · (3.1)','证明的起点',String.raw`\begin{gathered}d\deg\Sigma\leq K_X^3\leq64\chi(\omega_X)\\d\leq\frac{64\chi(\omega_X)}{p_g(X)-3}\end{gathered}`,
      'Miyaoka–Yau 不等式与典范像的次数下界结合，将问题归结为 Euler 示性数及 Albanese 纤维的估计。',
      'Starting the proof','Combine Miyaoka–Yau with the degree bound for the canonical image, then estimate the Euler characteristic using the Albanese fibration.')
  ]
};
// Section identifiers retain the paper numbering in either language.
for(const pages of Object.values(reportOutlines))for(const p of pages)if(p.kind!=='cover')p.en.source=p.source.replace('定理','Theorem').replace('引理','Lemma').replace('推论','Corollary');
