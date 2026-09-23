// Independently arranged bilingual seminar exposition.
// Mathematical source: Du–Hu, arXiv:2606.31170v1, §§1–3, CC BY 4.0.
// Each array is the intended writing order, not an automatically sliced paragraph.
const R=String.raw,M=tex=>({tex}),T=(text,enText)=>({text,enText});
function B(source,title,titleEn,boardLines){
  const tex=R`\begin{gathered}`+boardLines.filter(l=>l.tex).map(l=>l.tex).join(R`\\`)+R`\end{gathered}`;
  return {source,title,tex,layout:'flow',boardLines,editorialIndex:-1,
    text:boardLines.filter(l=>l.text).map(l=>l.text).join('\n'),
    en:{source,title:titleEn,text:boardLines.filter(l=>l.text).map(l=>l.enText).join('\n')},
    blocks:[{text:'',enText:'',tex}]};
}
export const huReport=[
 {kind:'cover',source:'报告',title:'一般型 Gorenstein 极小三维簇的典范映射次数',author:'胡勇',tex:'',text:'与 Jiabin Du 合作\narXiv:2606.31170',en:{source:'SEMINAR',title:'On the canonical degree of a Gorenstein minimal threefold of general type',author:'Yong Hu',text:'Joint work with Jiabin Du\narXiv:2606.31170'}},
 B('§ 1','典范映射与几何假设','Canonical map and hypotheses',[
  T('固定复数域上的射影三维簇 X。','Fix a projective threefold X over the complex numbers.'),
  M(R`X\text{ Gorenstein minimal},\quad K_X\text{ Cartier and nef}`),
  M(R`\kappa(X)=3,\qquad P:=p_g(X)=h^0(X,K_X)`),
  M(R`\phi_X:X\dashrightarrow\Sigma\subset\mathbb P^{P-1}`),
  T('假设典范映射到其像泛有限。','Assume that the canonical map is generically finite onto its image.'),
  M(R`\dim\Sigma=3,\qquad d=[\mathbb C(X):\mathbb C(\Sigma)]`)
 ]),
 B('§ 1 · 术语','典范线性系的移动部分','The moving canonical system',[
  T('消解典范线性系的不定点。','Resolve the base locus of the canonical system.'),
  M(R`\pi:\widetilde X\to X,\qquad\pi^*K_X=M+Z,\quad Z\geq0`),
  T('M 为无基点移动部分；Z 为固定部分。','M is basepoint free; Z is the fixed part.'),
  M(R`\widetilde\phi:\widetilde X\to\Sigma,\qquad M=\widetilde\phi^*\mathcal O_\Sigma(1)`),
  M(R`M^3=d\deg\Sigma,\qquad K_X^3=(\pi^*K_X)^3\geq M^3`),
  T('因此次数问题先转化为典范体积的估计。','Thus canonical volume gives the first control on the degree.')
 ]),
 B('§ 1','次数问题的背景','Earlier degree bounds',[
  T('以下次数界均在开头的三维几何假设下使用。','Use the following bounds under the opening threefold hypotheses.'),
  M(R`d\leq576\quad\text{Hacon (2004)}`),
  M(R`d\leq360\quad\text{Du--Gao (2016)}`),
  M(R`P>105411\ \Longrightarrow\ d\leq72\quad\text{Cai (2008)}`),
  T('目标是保持上界 72，同时降低几何亏格门槛。','Keep the bound 72 while lowering the genus threshold.'),
  M(R`P>243\quad\Longrightarrow\quad d\leq72`)
 ]),
 B('定理 1.2','新的几何亏格门槛','The new genus threshold',[
  T('X 为一般型 Gorenstein 极小三维簇。','Let X be a Gorenstein minimal threefold of general type.'),
  M(R`\phi_X\text{ generically finite},\qquad P>243`),
  M(R`d\leq72`),
  T('证明分两步：先控制典范体积，再分析 Albanese 纤维。','First control the volume, then study the Albanese fibres.'),
  M(R`d\deg\Sigma\leq K_X^3\leq64\chi(\omega_X)`),
  T('小几何亏格时存在次数 96 的例子，门槛不能直接去掉。','Small-genus examples have degree 96; the genus condition matters.')
 ]),
 B('定理 1.2','等号要求怎样的纤维','The fibre required by equality',[
  T('仍假设 p_g(X)>243，并设 d=72。','Retain p_g(X)>243 and suppose d=72.'),
  T('一般 Albanese 纤维 F 是光滑一般型极小曲面。','The general Albanese fibre F is a smooth minimal surface of general type.'),
  M(R`q(F)=0,\qquad p_g(F)=3`),
  M(R`K_F^2=36,\qquad\deg\phi_F=36`),
  T('等号来自纤维次数与底曲线次数同时达到上界。','Equality requires both the fibre and base degrees to be maximal.'),
  M(R`d=\deg\phi_F\cdot\deg\delta=36\cdot2`)
 ]),
 B('§ 1.1','Albanese 纤维化','The Albanese fibration',[
  M(R`q(X)=h^1(X,\mathcal O_X),\qquad a:X\to\operatorname{Alb}(X)`),
  T('取 Albanese 映射的 Stein 分解。','Take the Stein factorization of the Albanese map.'),
  M(R`X\xrightarrow{f}Y\longrightarrow\operatorname{Alb}(X)`),
  M(R`f_*\mathcal O_X=\mathcal O_Y,\qquad F=f^{-1}(y)\quad(y\text{ general})`),
  T('正则曲面指不规则度为零的曲面。','A regular surface is a surface of irregularity zero.'),
  M(R`F\text{ regular surface}\quad\Longleftrightarrow\quad\dim F=2,\ q(F)=0`)
 ]),
 B('§ 3 · 记号','Euler 示性数记录什么','The Euler characteristic',[
  M(R`\chi(\omega_X)=\sum_{i=0}^{3}(-1)^ih^i(X,\omega_X)`),
  T('用 Serre 对偶逐项改写。','Rewrite each term by Serre duality.'),
  M(R`h^0(\omega_X)=P,\qquad h^1(\omega_X)=h^2(\mathcal O_X)`),
  M(R`h^2(\omega_X)=q(X),\qquad h^3(\omega_X)=1`),
  M(R`\chi(\omega_X)=P-h^2(\mathcal O_X)+q(X)-1`),
  T('控制中间上同调和不规则度，才能把体积界变成次数界。','Cohomology and irregularity convert the volume bound into a degree bound.')
 ]),
 B('推论 2.3','Miyaoka–Yau 与 Riemann–Roch','Miyaoka–Yau and Riemann–Roch',[
  T('三维 Miyaoka–Yau 不等式给出：','In dimension three, Miyaoka–Yau gives:'),
  M(R`3K_X^3\leq8K_X\cdot c_2(X)`),
  T('Gorenstein 情形的 Riemann–Roch 等式为：','Gorenstein Riemann–Roch gives:'),
  M(R`K_X\cdot c_2(X)=24\chi(\omega_X)`),
  M(R`3K_X^3\leq192\chi(\omega_X)\quad\Longrightarrow\quad K_X^3\leq64\chi(\omega_X)`),
  T('常数 64 将贯穿后面的三个分支。','The constant 64 is used in all three subsequent cases.')
 ]),
 B('§ 3 · (3.1)','从典范体积到次数','From volume to degree',[
  T('典范像在射影空间中非退化，且维数为三。','The canonical image is a nondegenerate threefold.'),
  M(R`\operatorname{codim}(\Sigma,\mathbb P^{P-1})=P-4`),
  M(R`\deg\Sigma\geq\operatorname{codim}\Sigma+1=P-3`),
  M(R`d(P-3)\leq d\deg\Sigma\leq K_X^3\leq64\chi(\omega_X)`),
  M(R`d\leq\frac{64\chi(\omega_X)}{P-3}`),
  T('下一步分纤维类型估计分子。','Next estimate the numerator according to the fibre type.')
 ]),
 B('命题 3.1 · 推论 1.4','高次数迫使纤维正则','High degree forces a regular fibre',[
  T('假设一般 Albanese 纤维不是正则曲面。','Suppose the general Albanese fibre is not a regular surface.'),
  M(R`\chi(\omega_X)\leq P\qquad\text{Chen--Hacon (2006)}`),
  M(R`d\leq\frac{64P}{P-3}=64+\frac{192}{P-3}`),
  M(R`P>243\quad\Longrightarrow\quad d<65\quad\Longrightarrow\quad d\leq64`),
  T('最后一步使用次数为整数。取逆否命题得到：','Use that the degree is integral. The contrapositive is:'),
  M(R`P>243,\ d>64\quad\Longrightarrow\quad\dim F=2,\ q(F)=0`)
 ]),
 B('命题 3.2 · 记号','进入正则曲面纤维分支','Regular surface fibres',[
  M(R`f:X\to Y,\qquad b=g(Y)=q(X),\qquad s=p_g(F)`),
  T('F 是正则曲面；Y 是光滑曲线。','F is a regular surface and Y is a smooth curve.'),
  M(R`E=f_*\omega_X,\qquad\operatorname{rank}E=s,\quad h^0(Y,E)=P`),
  M(R`\chi(\omega_X)\leq P\left(1+\frac1s\right)\qquad\text{Chen--Hacon (2006)}`),
  M(R`\chi(\omega_X)=P-h^2(\mathcal O_X)+b-1\leq P+b-1`),
  T('乘性与加性两种估计，分别用于不同分支。','Use the multiplicative or additive estimate as the case requires.')
 ]),
 B('命题 3.2','直像丛的 Riemann–Roch','Riemann–Roch for the direct image',[
  M(R`V=f_*\omega_{X/Y},\qquad E=V\otimes\omega_Y`),
  T('使用相对典范直像的半正性：V 为 nef。','Use semipositivity of the relative canonical direct image: V is nef.'),
  M(R`\deg E=\deg V+s(2b-2)\geq s(2b-2)`),
  M(R`\chi(Y,E)=\deg E+s(1-b)\geq s(b-1)`),
  M(R`P=h^0(Y,E)\geq\chi(Y,E)\geq s(b-1)`),
  T('这些估计随后也用于强制截面在若干点消失。','The same estimates later produce sections vanishing at prescribed points.')
 ]),
 B('命题 3.2','证明的三个分支','The three cases',[
  T('始终保持 P>243；目标是控制 d。','Keep P>243 throughout; the goal is to bound d.'),
  M(R`s\geq9\quad\Longrightarrow\quad d<72`),
  M(R`s\leq8,\ b\leq7\quad\Longrightarrow\quad d<67`),
  M(R`s\leq8,\ b\geq8\quad\Longrightarrow\quad\text{analyse the generated rank}`),
  T('前两个分支只需数值估计。','The first two cases need only numerical estimates.'),
  T('第三个分支才需要典范像的纤维化与底曲线映射。','Only the third case needs the fibration of the canonical image.')
 ]),
 B('命题 3.2 · 情形 1','243 这个门槛如何出现','Where the threshold 243 comes from',[
  M(R`s\geq9\quad\Longrightarrow\quad1+\frac1s\leq\frac{10}{9}`),
  M(R`d\leq\frac{64P(1+1/s)}{P-3}\leq\frac{640P}{9(P-3)}`),
  M(R`\frac{640P}{9(P-3)}<72\quad\Longleftrightarrow\quad640P<648(P-3)`),
  M(R`648(P-3)-640P=8(P-243)>0`),
  T('于是这个分支严格小于 72。','Thus this case gives a strict bound below 72.'),
  T('等号情形必须留在纤维几何亏格较小的分支。','Equality can occur only in the small fibre-genus branch.')
 ]),
 B('命题 3.2 · 情形 2','底曲线亏格较小时的加性估计','Small base genus',[
  M(R`s\leq8,\qquad b\leq7`),
  M(R`\chi(\omega_X)=P-h^2(\mathcal O_X)+b-1\leq P+6`),
  M(R`d\leq\frac{64(P+6)}{P-3}=64+\frac{576}{P-3}`),
  M(R`P>243\quad\Longrightarrow\quad d<67`),
  T('这里不再使用含 s 的乘性估计。','Here use the additive bound without the factor involving s.'),
  T('因此等号 72 也不会在本分支出现。','This case cannot give equality at 72 either.')
 ]),
 B('命题 3.2 · 情形 3','在典范像上构造铅笔','A pencil on the canonical image',[
  M(R`s\leq8,\qquad b\geq8`),
  T('作双有理修改，使典范映射成为态射。','Make birational modifications so that the canonical map is a morphism.'),
  M(R`H\text{ very ample on }Y,\quad D_1,D_2\in|H|,\quad\operatorname{Supp}D_1\cap\operatorname{Supp}D_2=\varnothing`),
  M(R`\widetilde D_i=\phi_{X,*}f^*D_i\qquad(i=1,2)`),
  T('这两个除子张成的铅笔，在典范像上给出有理映射。','The two pushed-forward divisors span a pencil on the canonical image.'),
  M(R`\Sigma\dashrightarrow\mathbb P^1\quad\rightsquigarrow\quad\Sigma\xrightarrow{h}C\to\mathbb P^1`)
 ]),
 {source:'命题 3.2 · 情形 3',title:'典范像也纤维化',editorialIndex:-1,
  tex:R`\begin{gathered}s\leq8,\quad b\geq8\\h\circ\phi_X=\delta\circ f\\\phi_X(F_y)=h^{-1}(\delta(y))\quad(y\text{ general})\end{gathered}`,
  text:'消解铅笔的不定点并取 Stein 分解，得到右侧交换图。一般纤维 F_y 的典范像，就是 C 上对应的曲面纤维。随后用这个关系把截面的消失传到同一底曲线纤维上的所有点。',
  en:{source:'Proposition 3.2 · Case 3',title:'Fibering the canonical image',text:'Resolve the pencil and take its Stein factorization. The image of a general fibre F_y is the corresponding surface fibre over C. This will propagate the vanishing of a section to all points of the same base fibre.'},
  diagram:{kind:'canonical',title:'典范像的纤维化交换图',en:'Fibration of the canonical image',source:'arXiv:2606.31170v1, Proposition 3.2'}},
 B('§ 2.1 · 命题 3.2','评价映射与生成秩','Evaluation and generated rank',[
  M(R`E=f_*\omega_X,\qquad\operatorname{rank}E=s`),
  M(R`H^0(Y,E)\otimes\mathcal O_Y\xrightarrow{\mathrm{ev}}E`),
  M(R`E_{\mathrm{ev}}=\operatorname{im}(\mathrm{ev}),\qquad r=\operatorname{rank}E_{\mathrm{ev}}`),
  T('r 记录全局典范截面在一般纤维上生成的维数。','r measures the dimension generated on a general fibre by global sections.'),
  M(R`r<s\quad\text{or}\quad r=s`),
  T('先排除未满秩，再在满秩情形分解典范映射次数。','First treat deficient rank; then factor the degree in the full-rank case.')
 ]),
 B('命题 3.2 · 未满秩','秩估计如何排除高次数','The deficient-rank estimate',[
  T('对典范直像丛使用 Xiao (1986) 的生成秩估计。','Apply the Xiao (1986) generated-rank estimate to the canonical direct image.'),
  M(R`r<s:\qquad b-1\leq(b-1)(s-r)\leq r\leq s-1`),
  M(R`b\leq s\leq8`),
  M(R`\chi(\omega_X)\leq P+b-1\leq P+7`),
  M(R`d\leq\frac{64(P+7)}{P-3}=64+\frac{640}{P-3}<67`),
  T('所以剩下只需研究 r=s。','It remains to consider r=s.')
 ]),
 B('命题 3.2 · 满秩','限制映射满射与次数分解','Restriction and degree factorization',[
  M(R`r=s\quad\Longrightarrow\quad H^0(X,K_X)\twoheadrightarrow H^0(F,K_F)`),
  T('此时在一般纤维上得到完整的典范线性系。','The full canonical system is obtained on a general fibre.'),
  M(R`\phi_X|_F=\phi_F\quad\text{onto its image}`),
  M(R`e:=\deg\phi_F,\qquad m:=\deg\delta,\qquad d=e\,m`),
  T('一般底点有 m 个原像，每个曲面映射有 e 个原像。','There are m base preimages and e preimages in each surface fibre.'),
  M(R`e\leq36,\quad m\leq2\quad\Longrightarrow\quad d\leq72`)
 ]),
 B('命题 3.2 · 曲面次数','曲面上的 36 从何而来','Why the surface bound is 36',[
  M(R`s=p_g(F)\geq3,\qquad q(F)=0,\qquad\chi(\mathcal O_F)=s+1`),
  M(R`K_F^2\leq9\chi(\mathcal O_F)=9(s+1)`),
  M(R`\deg\phi_F(F)\geq s-2,\qquad e\deg\phi_F(F)\leq K_F^2`),
  M(R`e\leq\frac{9(s+1)}{s-2}=9+\frac{27}{s-2}\leq36`),
  T('若 e=36，上面的每个上界都必须取等。','If e=36, all the intervening upper bounds must be equalities.'),
  M(R`s=3,\qquad K_F^2=36,\qquad\deg\phi_F(F)=1`)
 ]),
 B('命题 3.2 · 底曲线估计','截面的零除子与最大性','A section with maximal zero divisor',[
  M(R`0\ne t\in H^0(Y,E),\qquad D_t=\operatorname{div}(t)`),
  T('在光滑曲线上，饱和截面给出一个线子丛。','On the smooth curve, saturation gives a line subbundle.'),
  M(R`\mathcal O_Y\xrightarrow{t}\mathcal O_Y(D_t)\hookrightarrow E`),
  T('选择零除子次数最大的 t；记 a 为这个次数。','Choose t with maximal zero-divisor degree, denoted by a.'),
  M(R`a:=\deg D_t,\qquad a>\tfrac32b\quad\text{or}\quad a\leq\tfrac32b`),
  T('两个分支都要推出底曲线映射次数 m≤2。','Both cases will give a base-map degree at most two.')
 ]),
 B('命题 3.2 · 底曲线估计','零除子怎样产生线性系','The linear system of the zero divisor',[
  M(R`\mathcal O_Y(D_t)\hookrightarrow E\quad\Longrightarrow\quad H^0(Y,D_t)\hookrightarrow H^0(Y,E)`),
  M(R`H^0(Y,E)=H^0(X,K_X)`),
  T('将底曲线上的截面拉回，得到典范线性系的子系。','Pulling back gives a subsystem of the canonical system.'),
  M(R`f^*|D_t|\subseteq|K_X|`),
  M(R`\psi_t:Y\dashrightarrow\Sigma_t,\qquad\psi_t=\eta_t\circ\delta`),
  T('当此映射非常值时，它的次数至少为 m。','When this map is nonconstant, its degree is at least m.')
 ]),
 B('命题 3.2 · 底曲线估计','大零除子：Riemann–Roch','Large divisor: Riemann–Roch',[
  M(R`a=\deg D_t>\frac32b`),
  M(R`h^0(Y,D_t)-h^1(Y,D_t)=a+1-b`),
  M(R`b<\frac23a\quad\Longrightarrow\quad h^0(Y,D_t)\geq a+1-b>\frac a3+1`),
  T('线性系的维数因此严格大于 a/3。','The dimension of the linear system is strictly greater than a/3.'),
  M(R`N:=h^0(Y,D_t)-1>\frac a3`),
  T('它定义到非退化射影曲线的非常值映射。','It defines a nonconstant map onto a nondegenerate projective curve.')
 ]),
 B('命题 3.2 · 底曲线估计','大零除子：次数严格小于三','Large divisor: degree below three',[
  M(R`\Sigma_t\subset\mathbb P^N\text{ nondegenerate}\quad\Longrightarrow\quad\deg\Sigma_t\geq N`),
  M(R`a\geq\deg\psi_t\cdot\deg\Sigma_t`),
  M(R`a>\deg\psi_t\cdot\frac a3\quad\Longrightarrow\quad\deg\psi_t<3`),
  T('除去固定部分只会降低线性系的次数。','Removing fixed components can only decrease the degree of the moving system.'),
  M(R`\psi_t=\eta_t\circ\delta\quad\Longrightarrow\quad m\leq\deg\psi_t\leq2`),
  T('大零除子分支完成。','This completes the large-divisor case.')
 ]),
 B('命题 3.2 · 底曲线估计','小零除子：指定消失点','Small divisor: prescribed vanishing',[
  M(R`a\leq\frac32b,\qquad D=y_1+\cdots+y_{b-2}\quad(y_i\text{ general})`),
  M(R`\deg E\geq s(2b-2),\qquad\deg E(-D)=\deg E-s(b-2)`),
  M(R`h^0(Y,E(-D))\geq\chi(Y,E(-D))`),
  M(R`\chi(Y,E(-D))=\deg E-s(b-2)+s(1-b)\geq s>0`),
  T('因此存在一个非零截面，在选定的 b−2 个点同时消失。','A nonzero section therefore vanishes at all the prescribed points.'),
  M(R`0\ne u\in H^0(Y,E(-D))\subset H^0(Y,E),\qquad D_u\geq D`)
 ]),
 B('命题 3.2 · 底曲线估计','消失为何传遍整个纤维','Why vanishing spreads along a base fibre',[
  T('选择一般点，使其像互异且避开分歧值。','Choose general points with distinct images away from branch values.'),
  M(R`u(y_i)=0\quad\Longleftrightarrow\quad u|_{F_{y_i}}=0`),
  T('对应的典范超平面包含整个曲面像。','The corresponding canonical hyperplane contains the entire surface image.'),
  M(R`\phi_X(F_y)=h^{-1}(\delta(y))`),
  M(R`\delta(y)=\delta(y_i)\quad\Longrightarrow\quad u|_{F_y}=0`),
  T('一个指定点的消失，迫使同一底曲线纤维上 m 个点都消失。','Vanishing at one chosen point forces vanishing at all m points over its image.')
 ]),
 B('命题 3.2 · 底曲线估计','小零除子：用最大性收束','Small divisor: finish by maximality',[
  M(R`D_u\geq\sum_{i=1}^{b-2}\delta^*(\delta(y_i))`),
  M(R`\deg D_u\geq m(b-2)`),
  T('t 的零除子次数最大，而当前分支的上界为 3b/2。','Maximality of t and the current case give the upper bound 3b/2.'),
  M(R`\frac32b\geq\deg D_t\geq\deg D_u\geq m(b-2)`),
  M(R`m\leq\frac{3b}{2(b-2)}\leq2\qquad(b\geq8)`),
  T('至此两个零除子分支都得到 m≤2。','Both zero-divisor cases now give m at most two.')
 ]),
 B('命题 3.2 · 证明收束','上界与等号的来源','The degree bound and equality',[
  M(R`r=s:\qquad d=e\,m\leq36\cdot2=72`),
  T('其余分支已经分别得到严格小于 72 的界。','All other cases already give a strict bound below 72.'),
  M(R`d=72\quad\Longrightarrow\quad e=36,\quad m=2`),
  M(R`p_g(F)=3,\quad q(F)=0,\quad K_F^2=36`),
  T('一般纤维光滑且极小；等号所需不变量全部得到。','The general fibre is smooth and minimal, with all the required invariants.'),
  M(R`P>243,\ d>64\quad\Longrightarrow\quad F\text{ is a regular surface}`)
 ]),
 B('例 3.3','次数 72 的乘积例子','A product attaining degree 72',[
  M(R`p_g(S)=3,\ q(S)=0,\ K_S^2=36,\ \deg\phi_S=36`),
  T('取这样的光滑极小曲面 S，及亏格 b≥2 的超椭圆曲线 C。','Take such a smooth minimal surface S and a hyperelliptic curve C of genus b≥2.'),
  M(R`X=S\times C,\qquad H^0(K_X)=H^0(K_S)\otimes H^0(K_C)`),
  M(R`p_g(X)=3b,\qquad q(X)=b`),
  M(R`\phi_X=\operatorname{Segre}\circ(\phi_S\times\phi_C),\qquad\deg\phi_X=36\cdot2=72`),
  T('取 b≥82，便有 3b>243，上界在定理范围内达到。','For b≥82, we have 3b>243, so equality occurs within the theorem’s range.')
 ])
];
