// Independently written reading-seminar notes, checked against KM98.
// Each section includes worked arguments; metadata states their exact scope and external inputs.
import {organizeBoards} from './board-flow.mjs';
import {KM_PROOFS} from './km-proof-boards.mjs';
const R=String.raw;
export const KM_CHAPTERS=[
 ['有理曲线与典范类','Rational curves and the canonical class'],
 ['极小模型纲领导论','Introduction to the minimal model program'],
 ['锥定理','Cone theorems'],
 ['极小模型纲领中的曲面奇点','Surface singularities of the minimal model program'],
 ['极小模型纲领中的奇点','Singularities of the minimal model program'],
 ['三维 flop','Three-dimensional flops'],
 ['半稳定极小模型','Semi-stable minimal models']
].map(([title,en],i)=>({id:i+1,title,en}));
export const KM_SECTIONS=[];
export const kmBoards=[];
function section(id,title,en,prerequisites,goal,raw){
 const chapter=Number(id.split('.')[0]),pages=raw.trim().split('\n').filter(Boolean).map((line,i)=>{
  const [heading,tex,text,headingEn,textEn]=line.split('|');
  if(line.split('|').length!==5||!textEn)throw new Error('Incomplete KM board '+id+' '+i);
  return {source:'§ '+id,title:heading,hideHeading:true,tex,text,chapter,section:id,en:{source:'§ '+id,title:headingEn,text:textEn}};
 });
 KM_SECTIONS.push({id,chapter,title,en,prerequisites,goal,boards:pages.length});kmBoards.push(...pages);
}
section('1.1','典范类为负时寻找有理曲线','Finding rational curves when K is negative','正规化、曲线上的 Riemann–Roch、射影族','理解变形维数、弯折与断裂、正特征约化如何配合。',R`
本节的目标与约定|X\text{ smooth projective},\quad n=\dim X,\quad -K_X\text{ ample}|称这样的 X 为 Fano 簇。目标是经过任意指定点构造有理曲线，并控制反典范次数。底域取代数闭域；正特征步骤另行注明。|The question and conventions|A smooth projective variety with ample anticanonical divisor is Fano. We seek a rational curve through each prescribed point, with a degree bound, over an algebraically closed field.
先看光滑曲面|2g(E)-2=(K_X+E)\cdot E,\qquad E\simeq\mathbf P^1,\ E^2=-1|代入伴随公式得到 K_X·E=−1。Castelnuovo 收缩定理（KM98，Thm 1.2）：光滑完备曲面可非平凡地收缩到光滑曲面，当且仅当存在负一曲线。|The surface prototype|Adjunction gives K_X·E=-1. KM98, Theorem 1.2 characterizes the existence of a nontrivial birational morphism to a smooth surface by a (-1)-curve.
光滑靶的例外纤维|f:Y\to X\text{ proper birational},\quad X\text{ smooth}|Abhyankar (1956)，Prop 1.3：每个非单点纤维被有理曲线覆盖。光滑性要求在靶 X；不能未经证明换成只有源 Y 光滑。|Exceptional fibres over a smooth target|Abhyankar (1956), Proposition 1.3: every fibre is a point or is covered by rational curves. Smoothness of the target is essential to the statement.
曲面情形的证明|\widetilde X\xrightarrow{q}Y\xrightarrow{f}X,\qquad f q=\pi|用点吹起解消逆映射，得到 π。π 的例外曲线均为有理曲线，且 q 满射到相应纤维。非恒定像由 Lüroth 定理仍为有理曲线。高维情形原书只给证明提纲。|Proof for surfaces|Resolve the inverse by point blow-ups. Their exceptional rational curves dominate the nontrivial fibres; Lüroth's theorem makes each nonconstant image rational. The higher-dimensional argument is only sketched in KM98.
有理映射的不定性|\Gamma\subset Z\times X,\quad p:\Gamma\to Z,\quad q:\Gamma\to X|设 Z 光滑、X 完备，Γ 为图闭包。若 q 在每个 p 纤维上恒定，正规性与适当性使映射下降；因此真正不定处必须留下非恒定的例外像。|Indeterminacy and graph closure|For smooth Z and proper X, take the graph closure. If q is constant on every p-fibre, the map descends by properness and normality. Genuine indeterminacy forces a nonconstant exceptional image.
没有有理曲线的推论|X\text{ proper, no rational curves}\quad\Longrightarrow\quad (Z\dashrightarrow X)\text{ extends}|Cor 1.4–1.5：不定处的例外像由有理曲线覆盖，所以无有理曲线时不存在不定处。这里 Z 必须光滑；此结论将用于一参数曲线族的总空间。|Extension in the absence of rational curves|Corollaries 1.4–1.5 eliminate indeterminacy when the proper target has no rational curves and the source is smooth. We will apply this to a surface parametrizing a family of curves.
刚性引理的全部假设|f:Y\to Z\text{ proper surjective},\quad\dim f^{-1}(z)=r|Lemma 1.6：Y 不可约，所有纤维连通且同维。若态射 g 把一个纤维压成点，则把每个纤维都压成点。连通与同维两项都需要保留。|Rigidity: hypotheses|In Lemma 1.6, Y is irreducible and all fibres of f are connected of the same dimension r. If a morphism g contracts one fibre to a point, it contracts every fibre.
刚性引理：联合像|Y\xrightarrow{h}W=\operatorname{im}(f,g)\xrightarrow{p}Z|在某点 z₀，p 纤维为零维。纤维维数上半连续，故在其邻域都是零维，h 的一般纤维维数为 r。再用上半连续性，所有 h 纤维维数至少为 r。|Rigidity: the joint image|Form the joint image W. A zero-dimensional p-fibre gives an open locus with zero-dimensional p-fibres. The general h-fibre has dimension r, hence every h-fibre has dimension at least r.
刚性引理：连通性收尾|h^{-1}(w)\subset f^{-1}(p(w)),\qquad\dim h^{-1}(w)\ge r|由于 f 纤维只有 r 维，h 的纤维只能由它的不可约分量组成。因此每个 p 纤维有限；它又是连通 f 纤维的像，所以只有一个点。|Rigidity: finish with connectedness|Each h-fibre is a union of components of an r-dimensional f-fibre. Thus the image of that fibre is finite. Connectedness makes this finite image a single point.
弯折断裂 I：输入|G:C\times D\to X,\qquad G(p,t)=g_0(p),\quad G_0=g_0|Cor 1.7：X 完备；C 光滑完备；D 为光滑连通曲线，允许不完备；g₀ 非恒定，且一般 G_t 与 g₀ 不同。这里要求映射变化，尚不要求像扫出曲面。|Bend and Break I: input|Corollary 1.7 assumes a proper X, smooth proper C, smooth connected D, a nonconstant g₀, a fixed image of p and genuinely varying maps. The images need not sweep a surface.
弯折断裂 I：结论|g_{0*}C\sim_{\rm alg}g_{1*}C+\sum_i a_iR_i,\qquad a_i>0|g₁ 可以恒定；各 R_i 为有理曲线，且至少一条经过 g₀(p)。结论是有效一循环的代数等价，不是所有一般成员都已经可约。|Bend and Break I: conclusion|The residual map g₁ may be constant. The R_i are rational and at least one contains g₀(p). This is algebraic equivalence of effective cycles, not reducibility of every general member.
为什么一定有不定点|G:C\times\overline D\dashrightarrow X|完备化 D。若沿整条 p×D̄ 无不定点，可取 p 的邻域 U，使 U×D̄ 上为态射。对到 U 的投影应用刚性引理，得到族在 U 上恒定，继而处处恒定，矛盾。|Why indeterminacy must occur|If the extension is defined along p×D̄, properness of D̄ gives a neighbourhood U with a morphism on U×D̄. Rigidity for the projection to U makes the family constant, a contradiction.
从不定点得到有理分量|\widetilde{C\times\overline D}\to C\times\overline D,\qquad F_d=C'_d+\sum_jm_jE_j|解消曲面上的不定性；特殊纤维由原曲线的严格变换和例外有理曲线组成。推前纤维循环得到前述代数等价；图闭包的非恒定例外像保证经过指定像点。|Extract the rational component|Resolve the surface map. The special fibre consists of the strict transform and exceptional rational curves. Push the fibre cycle forward; a nonconstant exceptional image through the prescribed point supplies the required component.
代数性不能去掉|E\text{ elliptic},\quad V=M\oplus M,\quad X=V/\Lambda|Blanchard (1956)，Example 1.8：正次数线丛上构造紧复环面纤维化，零截面可固定一点变形，却无有理曲线。到椭圆底的有理曲线恒定，环面纤维内也没有有理曲线。|Why algebraicity matters|Blanchard (1956), Example 1.8 constructs a compact complex torus bundle over an elliptic curve with moving pointed sections but no rational curves: a rational curve maps constantly to the base and cannot lie nontrivially in a torus fibre.
弯折断裂 II：更强输入|G:\mathbf P^1\times D\to X,\quad G(0,t)=x,\quad G(\infty,t)=y|Lemma 1.9：X 射影，固定两个像点，并要求 G 的像是曲面。此条件排除仅对同一条曲线重新参数化；只固定一个点不能推出新的分裂。|Bend and Break II: stronger input|Lemma 1.9 assumes projective X, two fixed image points, and a two-dimensional total image. The last condition excludes reparametrizations of a single curve.
弯折断裂 II：循环的重数|g_{0*}\mathbf P^1\sim_{\rm alg}\sum_i a_iR_i,\qquad\sum_i a_i\ge2|结论允许可约循环，也允许单一支撑上的多重循环。不能漏掉后一种。次数下降时，取支撑曲线同样能降低正次数，因其重数大于一。|Bend and Break II: retain multiplicities|The limiting rational cycle is reducible or multiple. A multiple cycle on one support also suffices for degree reduction; omitting multiplicities loses part of the lemma.
引理 1.9：无不定点时|A=\overline G^*H,\quad A^2>0,\quad A\cdot C_0=A\cdot C_\infty=0|把族延拓到 D̄ 上的射影直线丛 S。若映射已是态射，两条不交截面均被压缩。Hodge 指数定理使其自交为负；它们与 A 数值独立，却与 ρ(S)=2 矛盾。|Lemma 1.9: the morphism case|On a P¹-bundle compactification, the two disjoint contracted sections are orthogonal to a big nef pullback A. Hodge index gives negative self-intersections, so these three classes are independent, contradicting Picard number two.
引理 1.9：归纳的起点|S'\xrightarrow{r}S,\qquad r^*F=F_1+F_2|第一次吹起某个纤维上的不定点，两分量都是负一曲线。若推前循环已可约或多重就结束；反设每个有关特殊纤维的推前均不可约且约化。|Lemma 1.9: the first blow-up|Blowing up the first basepoint splits its fibre into two (-1)-curves. We are done if the pushed cycle is reducible or multiple; otherwise assume each relevant pushed special fibre is irreducible and reduced.
引理 1.9：排除剩余不定性|Q=F_1\cap F_2,\qquad \operatorname{mult}_{E}(F)\ge2\ \text{over }Q|在同一原纤维的另一点有不定性，会产生两个非零例外像，违背不可约性。在交点 Q 之上的例外分量重数至少二，因此必须全部压缩，否则违背约化性。|Lemma 1.9: remaining basepoints|A second distinct basepoint on the original fibre supplies another nonzero exceptional image, contradicting irreducibility. Exceptional components over Q have multiplicity at least two, so reducedness forces their contraction.
引理 1.9：初等变换结束归纳|S'\to S'',\qquad F_2\mapsto\text{point}|于是沿 F₂ 已无不定性。收缩 F₂ 得到另一个射影直线丛，解消所需吹起次数减少一。按此次数归纳，最终回到不可能的无不定点情形。|Lemma 1.9: elementary transformation|The map is defined along F₂. Contract it to obtain another ruled surface whose map needs one fewer blow-up. Induction reduces the assumed absence of a reducible or multiple fibre to the impossible morphism case.
Mori 定理的准确陈述|\forall x\in X\quad\exists R\ni x:\quad R\text{ rational},\quad0<-K_X\cdot R\le n+1|Mori (1982)，Thm 1.10：X 光滑射影且 −K_X 充沛。R 是既约曲线，其正规化为射影直线；定理不保证 R 本身光滑，也不预先指定其数值类。|Mori's theorem|Mori (1982), Theorem 1.10 applies to smooth projective Fano X. R is an integral curve with rational normalization; it need not be smooth and its numerical class is not prescribed.
变形理论输入|\dim_{[f]}\operatorname{Hom}(C,X)\ge h^0(C,f^*T_X)-h^1(C,f^*T_X)|取经过 x 的曲线并正规化为 f:C→X。切空间由 H⁰ 控制，障碍由 H¹ 控制，故得到下界。这里引用映射变形理论，不能把下界改写为维数等式。|The deformation-theoretic input|Normalize a curve through x to obtain f:C→X. Tangent and obstruction spaces give this lower bound. The deformation theorem is an explicit input, not an assertion that the Hom scheme is smooth.
Riemann–Roch 与固定一点|\begin{gathered}\chi(C,f^*T_X)=-K_X\cdot f_*C+n(1-g),\\\dim\operatorname{Hom}(C,X;f(p)=x)\ge -K_X\cdot f_*C-ng.\end{gathered}|向量丛秩为 n，次数为 −K_X·f_*C。固定一个像点至多加 n 个方程；右边大于零就有非恒定的一参数映射族，可以应用弯折断裂 I。|Riemann–Roch and one fixed point|The bundle has rank n and degree −K_X·f_*C. Fixing an image point imposes at most n equations. A positive lower bound supplies varying maps to which Bend and Break I applies.
亏格零和一|g=1:\quad \deg[m]=m^2,\qquad -K_X\cdot(f\circ[m])_*C=m^2d|记 d=−K_X·f_*C>0。亏格零时已有所求有理曲线。亏格一时先选原点，再复合倍乘映射；次数增长而亏格不变，取 m 大便有足够变形。|Genus zero and one|Put d=−K_X·f_*C>0. In genus zero the rational curve already exists. In genus one choose an origin and precompose by multiplication; its degree is m² while the genus stays fixed.
高亏格覆盖为何不够|g(C')=m(g(C)-1)+1,\qquad md-ng(C')=m[d-n(g-1)]-n|这是次数 m 的非分歧覆盖的 Riemann–Hurwitz 计算。次数与亏格同时增大，括号内未必为正；不能简单用任意高次覆盖代替 Frobenius。|Why ordinary covers do not suffice|For an unramified cover of degree m, Riemann–Hurwitz gives the displayed genus. The deformation bound need not become positive because genus grows together with degree.
把数据铺展到有限型整环|\mathcal X,\mathcal C,f,p\quad\text{over }A\subset k,\qquad A\text{ finite type over }\mathbf Z|收集方程、映射和指定点的系数，再局部化 A，使纤维光滑、亏格和交数固定，并保持相对反典范充沛。极大理想的剩余域为有限域。|Spread out all the data|Choose a finitely generated coefficient ring, then localize to preserve smoothness, genus, intersection numbers and relative anticanonical ampleness. Closed-point residue fields are finite.
Frobenius 的关键优势|F_q^e:C_s\to C_s,\qquad\deg F_q^e=q^e,\qquad q^ed-ng>0|在定义于有限域的纤维上，取适当 q 次 Frobenius。它不改变源曲线亏格，却将推前次数放大；固定有理点，弯折断裂 I 给出经过 x_s 的有理曲线。|The Frobenius advantage|On a fibre defined over a finite field, use a suitable q-power Frobenius. It preserves the source genus and fixes the marked rational point while multiplying degree. Bend and Break I now gives a rational curve through x_s.
固定两点后的维数|d=-K_X\cdot R>n+1\quad\Longrightarrow\quad\dim\operatorname{Hom}(\mathbf P^1,X;0,\infty)\ge d-n\ge2|固定两点的射影直线自同构群只有一维，因此至少有真正移动像的方向。选择扫出曲面的一参数子族，应用弯折断裂 II。|Two fixed points force moving images|If d>n+1, the two-pointed Hom space has dimension at least two, whereas automorphisms fixing 0 and infinity have dimension one. Choose a family whose images sweep a surface and apply Bend and Break II.
次数下降且保留指定点|R\sim_{\rm alg}\sum_i a_iR_i,\qquad0<-K_X\cdot R_i<d|从极限支撑中选一条经过 x_s 的分量。充沛性保证各分量次数为正；可约或多重性保证所选分量次数严格下降。重复过程在正整数上终止，得到 d≤n+1。|Lower degree while retaining the point|Select a component through x_s. Ampleness makes every component degree positive, and reducibility or multiplicity makes the chosen degree strictly smaller. Descent among positive integers ends at d≤n+1.
回到特征零：有界参数空间|\deg_H R_s\le m(n+1),\qquad H=-mK_X\text{ very ample}|固定同一 m，所有好纤维上的曲线次数有统一上界。对有限多个次数，考虑带指定点的非恒定射影直线映射的有限型参数空间；无公共零点等条件取开集。|Returning to characteristic zero: bounded parameters|Fix a relative embedding by −mK_X. Only finitely many degrees occur. Use finite-type spaces of nonconstant maps from P¹ of these degrees with the marked image condition, imposing basepoint freeness as an open condition.
回到特征零：稠密性而非猜测|\operatorname{im}(T\to\operatorname{Spec}A)\text{ constructible and dense}\quad\Longrightarrow\quad\eta\in\operatorname{im}(T)|参数空间的像包含稠密的好闭点；Chevalley 定理使该像可构造，所以包含非空开集及泛点。几何泛纤维非空，扩域后给出原特征零上的曲线。|Why the generic fibre is nonempty|The finite union of parameter-space images contains a dense set of good closed points. Its constructible image contains an open subset and the generic point. Passing to the geometric generic fibre yields a curve after extension of the ground field.
上界的例子与本节讨论|X=\mathbf P^n,\qquad -K_X=(n+1)H,\qquad H\cdot\ell=1|直线恰好达到 n+1 的上界。请讲者解释三个区别：映射变动与像变动；可约循环与多重循环；无界的逐特征存在与有界参数空间。本次只完成 §1.1。|Sharpness and discussion|Lines in projective space attain the bound n+1. Explain the distinctions between moving maps and moving images, reducible and multiple cycles, and fibrewise existence versus a bounded parameter space. This session ends with §1.1.
`);
section('1.2','典范类非 nef 时寻找有理曲线','Finding rational curves when K is not nef','§1.1；nef 与充沛除子','把一条负曲线转化为有次数控制的有理曲线。',R`
从一条负曲线出发|K_X\cdot C<0,\qquad M=\frac{-K_X\cdot C}{H\cdot C}>0|设 X 光滑射影，H 为充沛 Cartier 除子。负曲线 C 可能有高亏格；本节要保持斜率信息，同时得到有理曲线。|Start with a negative curve|Fix an ample Cartier divisor H on a smooth projective variety and a K-negative curve C.
加权平均引理|\frac{a+b}{c+d}\le\max\left\{\frac ac,\frac bd\right\},\qquad c,d>0|把左式写成右侧两个斜率的加权平均即得证明。退化循环分裂后，至少一个分量保留原来的斜率下界。|The weighted-average step|A ratio of sums is a weighted average of the component ratios; one component retains the lower bound.
断裂过程如何终止|H\cdot C_{j+1}<H\cdot C_j,\qquad H\cdot C_j\in\mathbf Z_{>0}|每次选择较低 H 次数的剩余分量。严格下降的正整数给出有限过程；不能仅凭几何图像断言断裂会终止。|A decreasing integer|The remaining component has strictly smaller positive integral H-degree, so the iterative breaking process terminates.
有理曲线的次数控制|0<-K_X\cdot R\le n+1,\qquad H\cdot R\le\frac{n+1}{M}|这是定理 1.13 的斜率控制所给出的结果。证明提纲：先在正特征保持斜率，再将过大反典范次数的有理曲线继续分裂。|The controlled rational curve|The slope estimate and the anticanonical bound yield a uniform H-degree bound in Theorem 1.13.
为何有界性不可省略|H\cdot R\le B\quad\Longrightarrow\quad\text{bounded cycle parameter spaces}|传播回特征零需要同一有界参数空间。若每个素特征仅给出次数任意增大的曲线，则这些存在性结论无法直接拼接。|Why bounded degree matters|A common bounded cycle space is needed to lift existence from varying positive characteristics.
结论与定位的区别|K_X\ \text{not nef}\quad\Longrightarrow\quad\exists R\simeq_{\rm bir}\mathbf P^1,\ K_X\cdot R<0|讨论：本节的次数论证并没有自动指定有理曲线经过哪个点。把存在、经过指定点、覆盖性分别陈述，再比较 §1.1 的 Fano 情形。|Existence versus location|Distinguish existence, passing through a prescribed point, and covering a locus; they are different assertions.
`);
section('1.3','光滑簇的曲线锥','The cone of curves of smooth varieties','数值等价、有限维凸锥','在数值空间中理解极端射线以及收缩的含义。',R`
先区分两个数值空间|N_1(X)=Z_1(X)_{\mathbf R}/\equiv,\qquad N^1(X)=\operatorname{NS}(X)\otimes\mathbf R|在射影情形，除子与曲线的交数给出对偶。这里的等价关系只记录全部 Cartier 除子的交数，不是有理等价。|Numerical spaces|Intersection pairs numerical divisor and curve spaces; numerical equivalence is weaker than rational equivalence.
闭包是定义的一部分|\overline{\operatorname{NE}}(X)=\overline{\sum_{C\subset X}\mathbf R_{\ge0}[C]}|有效曲线锥的边界可能由极限类组成，不一定每个边界点都由单条曲线表示。讨论时应始终保留闭包记号。|The closure matters|Boundary classes can be limits and need not all be represented by individual curves.
极端射线的定义|u+v\in R,\quad u,v\in\overline{\operatorname{NE}}(X)\quad\Longrightarrow\quad u,v\in R|R 是一维面。定义是关于整个闭凸锥的分解性质，而不是某幅二维示意图里看起来位于最外侧。|An extremal ray|Extremality is a decomposition property inside the whole closed cone, not just an edge in a drawing.
曲面负曲线的检验|E^2<0,\quad E\ne C\quad\Longrightarrow\quad E\cdot C\ge0|对不可约有效曲线使用交点重数非负。除 E 本身外，其他曲线类都落在相应非负半空间，由此证明 E 张成极端射线。|Negative curves on surfaces|Nonnegative intersections of distinct integral curves separate the negative self-intersection ray from all other effective classes.
收缩必须满足两项条件|f_*\mathcal O_X=\mathcal O_Z,\qquad f(C)=\mathrm{pt}\Longleftrightarrow[C]\in F|定义 1.25 同时规定被压缩的曲线和 Stein 条件。仅画出某条曲线被压缩，并未证明存在代数簇上的射影收缩。|What a contraction means|Both the contracted curves and the Stein condition are required. Contractibility is an additional theorem.
吹起平面的完整例子|X=\operatorname{Bl}_p\mathbf P^2,\quad\overline{\operatorname{NE}}(X)=\mathbf R_{\ge0}[E]+\mathbf R_{\ge0}[H-E]|计算 H²=1、H·E=0、E²=-1。两条射线分别给出吹降和平面过一点直线束的纤维化；后者不是双有理收缩。|Blowing up the plane|The two rays give the blow-down and the ruling by lines through p. Only the first is birational.
`);
section('1.4','曲面的极小模型','Minimal models of surfaces','§1.3；伴随公式；曲面 Riemann–Roch','完整分析负极端射线的三种收缩并证明算法终止。',R`
三种几何结局|C^2<0,\qquad C^2=0,\qquad C^2>0|设 X 是光滑射影曲面，C 张成 K 负极端射线。定理 1.28 按自交符号区分吹降、到曲线的纤维化和到一点的收缩。|Three cases|For a K-negative extremal ray on a smooth projective surface, split the argument by the sign of C².
负自交迫使负一曲线|2p_a(C)-2=C^2+K_X\cdot C\le-2|两个交数都是负整数，左端至少为 -2，故只能等号：算术亏格为零且两个交数均为 -1。不可约曲线算术亏格零遂为光滑有理曲线。|Deriving a (-1)-curve|Adjunction forces arithmetic genus zero and both intersections equal to -1, hence a smooth rational curve.
零自交产生线性系|\chi(\mathcal O_X(mC))=\chi(\mathcal O_X)-\frac m2K_X\cdot C|右端线性增长。结合高阶上同调消失、固定分量分析和 C²=0，得到一个无基点倍数，再经 Stein 分解得到到曲线的收缩。|The zero-square case|Riemann–Roch grows linearly. Control fixed components and use C²=0 to obtain a free multiple and a ruling.
正自交迫使 Picard 数为一|C^2>0\Longrightarrow[C]\in\operatorname{Int}\overline{\operatorname{NE}}(X),\qquad\rho(X)=1|使用原书的曲面正锥论证。一个内点同时张成极端射线，迫使锥一维；于是负典范类充沛。这一步不能直接用于高维自交类。|The positive-square case|The surface argument places C in the interior; extremality then forces Picard number one and anticanonical ampleness.
终止靠 Picard 数下降|\rho(X_{i+1})=\rho(X_i)-1|每次双有理极端收缩都降低 Picard 数，因此有限次后典范类 nef，或者得到 Mori 纤维空间。纤维型步骤是终点而非继续吹降。|Termination on surfaces|Birational contractions lower the Picard number. Stop at a nef canonical class or a fibre-type contraction.
极小曲面与极小模型的措辞|K_X\ \text{nef}\quad\Longrightarrow\quad\text{no }(-1)\text{-curves}|讨论：无负一曲线不总意味着典范类 nef，例如射影平面和某些有理直纹曲面。原书在此使用 nef 典范类作为极小模型的条件。|Minimal surface terminology|The absence of (-1)-curves alone does not imply nef K; the projective plane is an immediate counterexample.
`);
section('1.5','充沛性判据','Ampleness criteria','交数、Euler 特征、Serre 消失','明确 nef、严格 nef、充沛和相对充沛之间的区别。',R`
交数来自 Euler 多项式|\chi\bigl(X,\mathcal O_X(mL)\bigr)=\frac{L^n}{n!}m^n+O(m^{n-1})|设 X 为 n 维适当概形，L 为 Cartier 除子。弱 Riemann–Roch 只确定最高次项；本章不需要完整的 Todd 类公式。|The leading coefficient|Weak Riemann–Roch identifies the top coefficient of the Euler polynomial without requiring the full Riemann–Roch formula.
Nakai–Moishezon 判据|L\ \text{ample}\Longleftrightarrow L^{\dim Z}\cdot Z>0\quad\text{for every positive-dimensional }Z|对适当代数簇上的 Cartier 除子，必须检查每个正维不可约子簇。只检查顶自交，或者只检查所有实际曲线，都不足以代替该判据。|Nakai–Moishezon|Positivity is required on every positive-dimensional integral subvariety, not merely on X or on individual curves.
nef 的混合交数|L\ \text{nef},\quad A\ \text{ample}\quad\Longrightarrow\quad L^{n-i}A^i\ge0|证明思路：超平面截面归纳，并研究交数多项式。取小的充沛扰动再极限，得 nef 的顶自交非负；这不是严格正性。|Intersections of nef divisors|Use hyperplane induction and ample perturbations to obtain nonnegative intersection numbers, including the top self-intersection.
Kleiman 判据中的闭锥|L\ \text{ample}\Longleftrightarrow L\cdot z>0\quad(0\ne z\in\overline{\operatorname{NE}}(X))|在射影情形，正性施加于闭锥中每个非零类。严格 nef 只测试实际曲线；非零极限类可能使交数趋于零，这是两者的关键差别。|Kleiman's criterion|Test every nonzero class in the closed cone. Strict positivity on actual curves is a weaker condition.
相对充沛的局部性|L\vert_{X_y}\ \text{ample}\Longrightarrow L\ \text{ample over some }U\ni y|命题 1.41：由纤维上的 Serre 消失、相干直像和 Nakayama 引理，提升局部生成截面，得到邻域上的相对充沛性。|Relative ampleness is local|Fibrewise Serre vanishing, coherent direct images and Nakayama lift sections to a neighbourhood of the base point.
相对 nef 的一个陷阱|X=E\times E,\quad D=\Gamma_{\mathrm{id}}-(E\times\{0\}),\quad(D+f^*A)^2=-2|f 是到第一因子的投影。D 在每条纤维上次数零，但加任意底空间除子的拉回仍不 nef。讨论：对相对充沛为何可以加足够多的拉回？|A relative-nef pitfall|On an elliptic product this fibrewise degree-zero divisor remains non-nef after adding any pullback from the base.
`);
section('2.1','Mori 纲领导论',"Introduction to Mori's program",'第一章；正规簇与 Weil 除子','理解奇点、除子收缩和 flip 为什么不可避免。',R`
工作范畴要先固定|X\ \text{normal},\quad K_X\ \mathbf Q\text{-Cartier},\quad\rho(X)<\infty|以下以复数域上的射影簇为全局背景。讨论终端奇点与有理 Cartier 条件；不能在典范类尚不可拉回时直接写出 discrepancy。|Fix the category|Work over the complex numbers with normal projective varieties and a Q-Cartier canonical divisor.
光滑中心的吹起公式|K_{\widetilde X}=f^*K_X+(c-1)E|f 是沿光滑余维 c 中心的吹起。局部坐标的 Jacobian 给出系数 c-1，解释了终端奇点中正 discrepancy 的自然来源。|The blow-up formula|The local Jacobian gives coefficient c-1 for a smooth centre of codimension c.
除子收缩与小收缩|\operatorname{codim}_X\operatorname{Exc}(f)=1\quad\text{or}\quad\ge2|除子收缩移除一个除子；小收缩只压缩更高余维集合。后者的像通常不再具有适当的有理 Cartier 典范类，不能直接继续纲领。|Divisorial versus small|A small contraction can leave a target whose canonical divisor is not Q-Cartier, preventing a direct next step.
flip 的正性反转|X\xrightarrow{f}Z\xleftarrow{f^+}X^+,\qquad -K_X\text{ is }f\text{-ample},\ K_{X^+}\text{ is }f^+\text{-ample}|两边都小，双有理映射在余维一同构。flip 并不是任意换一个双有理模型；它须满足同一底空间上的指定正性。|The sign change in a flip|Both contractions are small over the same base, and canonical positivity reverses across the birational map.
终端与典范奇点|a(E,X)>0\ \text{or}\ a(E,X)\ge0\qquad(E\text{ exceptional})|这里先取边界为零，并且只对例外除子取条件。原书把终端奇点用于极小模型，典范奇点用于典范模型；二者不是光滑的同义词。|Terminal and canonical|With zero boundary, test positive or nonnegative discrepancies on exceptional divisors over X.
纲领的三项难题|\text{contractions}\quad+\quad\text{existence of flips}\quad+\quad\text{termination}|先有负射线的收缩，再问小收缩的 flip 是否存在，最后问序列是否停止。讨论班按原书的维数和假设陈述结果，不把这些任务混为一项。|Three separate problems|Contraction, flip existence and termination are logically distinct. Keep the original dimensional hypotheses visible.
`);
section('2.2','纲领的推广','Extensions of the minimal model program','§2.1；相对交数','把相对、对数和等变版本的输入说清楚。',R`
相对曲线空间|N_1(X/S)=\langle[C]:f(C)=\mathrm{pt}\rangle_{\mathbf R}/\equiv_S|相对正性只测试被 f 压缩的曲线。它不测试映满底空间曲线的水平曲线，因此不能直接替换为绝对正性。|Relative numerical classes|Relative positivity tests contracted curves only; horizontal curves impose different conditions.
相对 Picard 数|\rho(X/S)=\dim N^1(X/S),\qquad\rho(X/Z)=1|极端收缩在其目标 Z 上具有相对 Picard 数一。原来的底空间 S 和当前收缩目标 Z 是两个不同角色，要在图中分别标记。|Two different bases|Distinguish the fixed base S from the current contraction target Z; relative Picard rank one concerns X over Z.
对数典范除子|B=\sum b_iB_i,\quad0\le b_i\le1,\quad K_X+B\ \mathbf Q\text{-Cartier}|加入边界后研究 K+B 的正性。只知道 K 与 B 是 Weil 除子，不足以定义所需拉回；需要和为有理 Cartier。|Pairs and their log canonical divisor|The required pullback is that of K+B. The individual Weil divisors need not both be Cartier.
相对极小模型与纤维空间|K_{X'}+B'\ \text{nef}/S\quad\text{or}\quad X'\to Z\to S|纤维型结局还要求维数下降、相对 Picard 数一及负对数典范类相对充沛。仅有一个纤维化不能称为 Mori 纤维空间。|The two outcomes|A Mori fibre space also requires lower-dimensional base, relative Picard rank one and relative anticanonical ampleness.
等变操作为什么改用面|G\curvearrowright X,\qquad F=\sum_{g\in G}gR|有限群可能置换负射线，单独收缩一条会破坏群作用。必须检查轨道张成的面是否具有相容的收缩，不能随意逐条处理。|Equivariant choices|A group may permute rays. Equivariant contractions require a compatible invariant face, not an arbitrary chosen ray.
一个相对与绝对的练习|\pi:\mathbf P^1\times C\to C,\qquad -K_X\cdot\mathbf P^1=2|即使 C 的亏格很大，负典范类在投影的纤维上仍为正。计算水平截面的交数，验证相对 Fano 并不推出整体 Fano。|Relative does not mean absolute|Compute vertical and horizontal intersections on a product with a curve of large genus.
`);
section('2.3','纲领中的奇点','Singularities in the minimal model program','解消；除子拉回；§2.1','区分 discrepancy、log discrepancy，以及 klt、plt、dlt、lc。',R`
固定 discrepancy 约定|K_Y+f_*^{-1}B=f^*(K_X+B)+\sum_{E\ \mathrm{exc}}a(E,X,B)E|f 为对数解消。板书用 a 表示 discrepancy，A=a+1 表示 log discrepancy；原书 discrep 只对例外除子取下确界。|The discrepancy convention|Use a for discrepancy and A=a+1 for log discrepancy. KM's discrep is an infimum over exceptional divisors.
边界本身的系数|a(B_i,X,B)=-b_i,\qquad A(B_i,X,B)=1-b_i|把测试扩展到所有除子时，X 上的边界分量也参与。因此 klt 需要边界系数严格小于一；只检查解消上的例外除子是不够的。|Divisors already on X|The boundary itself matters when testing all divisorial valuations, especially for klt.
一次吹起的局部计算|a(E,X,B)=c-1-\sum_{Z\subset B_i}b_i|设中心 Z 光滑、余维 c，并与简单正规交叉边界相容。以典范吹起公式减去边界的总变换，逐项得到该系数。|Compute on a blow-up|For a smooth compatible centre, subtract the boundary multiplicities from the canonical coefficient c-1.
klt 与 lc 的严格性|\mathrm{klt}:A(E,X,B)>0;\qquad\mathrm{lc}:A(E,X,B)\ge0|此处量词为所有除子 E。光滑 snc 有效边界的情形分别等价于每个系数小于一、或不超过一；这提供最基本的可计算模型。|klt and lc|For effective snc boundaries on a smooth variety, the conditions become coefficient bounds below one or at most one.
plt 与 dlt 不可混淆|X=\mathbf A^2,\quad B=(x=0)+(y=0),\quad a(E,X,B)=-1|两条坐标轴的配对为 dlt，却不为 plt：吹起交点就得到 discrepancy -1。dlt 允许边界的 snc 交层，plt 的例外除子条件更强。|dlt is not plt|Two coefficient-one coordinate axes form a dlt pair; blowing up their intersection shows it is not plt.
勘误的预备提醒|\operatorname{discrep}(X,B)\ne\inf_E A(E,X,B)|本节约定会在 §5.2 的 Lemma 5.17(2) 反例中再次使用。讨论：为什么知道某个解消已经 snc，仍可能需要进一步吹起交层？|Prepare for the erratum|A log resolution does not remove the need to consider valuations from further blow-ups of strata.
`);
section('2.4','Kodaira 消失定理','The Kodaira vanishing theorem','光滑射影簇的上同调、Serre 对偶','说明经典消失的假设和循环覆盖证明路线。',R`
定理的准确输入|H^q(X,\omega_X\otimes L)=0\qquad(q>0)|X 光滑复射影，L 充沛。光滑性、特征零和正性均有作用；不能把该式直接用于任意奇异簇或正特征。|Kodaira vanishing|Assume X smooth complex projective and L ample. Each of these hypotheses matters.
用对偶改写指标|H^i(X,L^{-1})=0\qquad(i<n)|由 Serre 对偶，上式等价于前一板。注意消失范围从正次数变为低于维数，不能在两种写法中保留同一指标条件。|Dual form|Serre duality converts positive cohomological degree into degrees below the dimension.
循环覆盖的代数|\pi_*\mathcal O_Y=\bigoplus_{j=0}^{m-1}L^{-j},\qquad D\in\lvert mL\rvert|取光滑分支除子，在适当局部平凡化下写 t^m=s。覆盖上的层分解使原来的逆线丛成为直像的特征子空间。|The cyclic cover|A smooth branch divisor gives a cyclic cover whose eigensheaves include the negative powers of L.
证明所调用的分析输入|H^k(Y,\mathbf C)=\bigoplus_{p+q=k}H^q(Y,\Omega_Y^p)|证明路线：使用代数与解析上同调比较及 Hodge 理论处理覆盖。讨论班把这些标为引用结果，不把分解公式本身说成完整消失证明。|The Hodge-theoretic input|The cover argument invokes comparison and Hodge theory. These are stated inputs, not proved merely by displaying a decomposition.
截面延拓的基本应用|0\to L(-D)\to L\to L\vert_D\to0|若 H¹(X,L(-D))=0，则全局截面到 D 上截面的限制满射。后面的无基点证明反复使用这一机制，但每次都要核对被减去的除子。|Extending sections|Vanishing of H¹ of the kernel makes restriction on global sections surjective.
边界条件的反例练习|X\text{ elliptic},\quad L=\mathcal O_X,\quad H^1(X,\omega_X)\ne0|L 是 nef 但不充沛，经典 Kodaira 结论已经失败。下一节加入 big 条件，而不是简单把定理中的 ample 一词删掉。|Why nef alone is insufficient|The trivial bundle on an elliptic curve is nef but gives nonvanishing H¹ of the canonical bundle.
`);
section('2.5','Kodaira 消失的推广','Generalizations of Kodaira vanishing','§2.3–2.4；nef 与 big','掌握取整、分数边界及相对消失的使用方式。',R`
先定义 big|h^0(X,\mathcal O_X(mD))\ge c\,m^n\quad(m\gg0\text{ divisible})|对 Cartier 或有理 Cartier 除子，以最高阶截面增长描述 big。一般 big 除子不一定 nef，二者在本节要同时出现。|Bigness|Bigness measures top-order growth of sections; it does not imply nefness.
Kawamata–Viehweg 消失|H^q(X,\mathcal O_X(K_X+\lceil M\rceil))=0\qquad(q>0)|X 光滑复射影，M 为 nef 且 big 的有理除子，分数部分支撑 snc。Kawamata (1982)、Viehweg (1982)。先检查取整方向，再套用定理。|Kawamata–Viehweg vanishing|Assume nef and big M with snc fractional support on smooth complex projective X; the divisor is rounded up.
边界形式的核对|D-(K_X+B)\ \text{nef and big},\qquad H^q(X,\mathcal O_X(D))=0|取光滑 snc 配对、有效有理边界 B 且系数小于一，D 为 Cartier。此版本等价于适当取整的写法，不能忽略整数与分数部分。|The boundary formulation|For a smooth snc klt boundary and Cartier D, positivity of D-(K+B) yields vanishing.
相对消失的用途|R^q f_*\mathcal O_Y(K_Y+\lceil M\rceil)=0\qquad(q>0)|在光滑 Y 上，M 对 f nef 且 f-big，分数支撑 snc，f 射影。此处引用相对形式；双有理情形随后用于比较奇点上的层。|Relative vanishing|Use the relative theorem for a projective morphism with relative nefness and bigness, checking the snc hypothesis.
证明路线而非省略的等号|\text{log resolution}\ \longrightarrow\ \text{rounding}\ \longrightarrow\ R^qf_*=0|推广到 klt 奇点要在解消上安排边界与例外项，再正确下推。尤其不能先假设奇点已有理性，因为第五章正要由消失推出它。|Avoid a circular proof|Arrange the rounded exceptional divisor upstairs and push down; do not assume rational singularities before proving them later.
应用前的四项核查|D\ \text{Cartier};\quad B\ge0;\quad (X,B)\ \mathrm{klt};\quad D-K_X-B\ \text{nef and big}|讨论：移除 big、把 klt 改成任意 lc、或把 Cartier 换成任意 Weil 时，哪一步不再合法？区分本节已证版本和需要额外定理的版本。|Check before applying|Track Cartierness, boundary effectiveness, klt singularities and nef-and-big positivity separately.
`);
section('3.1','锥定理证明的组织','Organizing the cone theorem','§2.3–2.5','区分依赖顺序与原书叙述顺序。',R`
本章固定的配对|(X,B)\ \mathrm{klt},\quad B\ge0,\quad K_X+B\ \mathbf Q\text{-Cartier}|除另有说明外，底域特征零，X 正规射影，边界为有理除子。每次下推到收缩目标后，都要重新核查这些假设。|Standing assumptions|Work over characteristic zero with a normal projective klt pair and an effective rational boundary.
四个定理的逻辑链|\text{nonvanishing}\Rightarrow\text{basepoint-free}\Rightarrow\text{rationality}\Rightarrow\text{cone}|这是证明的依赖图，不是本章小节的排列。讨论班先给出目标，再把非消失作为暂引结果，最后回到 §3.5 补足证明路线。|Dependencies|Nonvanishing precedes basepoint-freeness, rationality and the cone theorem logically, even when exposition uses another order.
支持超平面的作用|L\cdot z=0,\qquad L\cdot\overline{NE}(X)\ge0|由凸几何寻找 nef 支持类只是第一步。为了产生代数态射，还需要支持类有理，并由无基点定理获得截面。|From convex geometry to geometry|A nef support functional alone gives no morphism. Rationality and semi-ampleness supply the algebraic contraction.
非消失还不是半充沛|H^0(X,mL)\ne0\quad\not\Rightarrow\quad\operatorname{Bs}\lvert mL\rvert=\varnothing|有一个非零截面只给一个有效除子。下一阶段需要让基点集逐步缩小，并保证最后消失，不能将两个命题混为一谈。|Nonvanishing versus generation|One section gives an effective divisor, not generation at every point.
收缩后的两种维数|\dim Y<\dim X\quad\text{or}\quad\dim Y=\dim X|有纤维型收缩，也有双有理收缩。双有理时还须区分除子型与小收缩；只有后者才进入 flip 问题。|Classify the contraction|Separate fibre type, divisorial contractions and small birational contractions before discussing flips.
讨论班的证明责任|\text{hypotheses}\to\text{vanishing}\to\text{sections}\to\text{morphism}|本章把深层输入明确标成引用。每次报告至少解释一个截面延拓步骤和一个数值不等式，避免只串联定理名称。|Proof obligations|Track a vanishing statement, the resulting sections and the morphism they define; label deeper inputs explicitly.
`);
section('3.2','无基点定理','Basepoint-free theorem','§2.5；§3.5 非消失作为输入','把非消失升级为充分大倍数的全局生成。',R`
定理 3.3 的假设|D\ \text{nef Cartier},\quad aD-(K_X+B)\ \text{nef and big},\quad a>0|X 为特征零完备簇，配对 klt 且 B 有效。本讨论取射影情形。注意 D 是 Cartier；仅仅有理 Cartier 时要先取整倍数。|Theorem 3.3: assumptions|For a projective klt pair with effective boundary, take nef Cartier D with the stated nef-and-big difference.
结论中的量词|\operatorname{Bs}\lvert mD\rvert=\varnothing\qquad(m\gg0)|结论为每个充分大的整数 m，强于只找到一个倍数。特别地 D 半充沛，定义的态射与 D 的数值零方向相关。|Quantifiers|All sufficiently large integral multiples are basepoint-free, in particular D is semi-ample.
先获得有效除子|H^0(X,\mathcal O_X(mD))\ne0\qquad(m\gg0)|此处引用 §3.5。若线性系起初为空，无从讨论缩小固定部分；因此非消失是不能跳过的独立输入。|Start with a section|Nonvanishing is a separate input, needed before discussing the fixed locus.
延拓截面的关键正合列|0\to\mathcal I_Z(mD)\to\mathcal O_X(mD)\to\mathcal O_Z(mD)\to0|证明提纲：构造适当中心 Z，并用消失得到限制映射满射。构造 Z 和验证正性是证明的实质，此式本身不保证延拓。|The extension step|Construct a suitable centre and prove vanishing for the kernel. The exact sequence alone does not supply surjectivity.
基点集下降的有限性|\operatorname{Bs}\lvert m_1D\rvert\supsetneq\operatorname{Bs}\lvert m_2D\rvert\supsetneq\cdots|证明提纲：控制倍数，使闭子集形成下降链；Noether 性保证有限。最终还要处理整除关系，才得到所有充分大倍数的结论。|Shrinking the base locus|A controlled descending chain stabilizes by Noetherianity; divisibility arguments complete the all-large-multiples conclusion.
检查错误推广|D\equiv0,\quad D\text{ non-torsion in }\operatorname{Pic}^0(E)|椭圆曲线上非扭零次数线丛是 nef，却没有正倍数截面。这里正性差不 big，说明定理的附加假设不是形式条件。|A boundary example|A nontorsion degree-zero line bundle on an elliptic curve is nef but not semi-ample; the big hypothesis fails.
`);
section('3.3','锥与收缩','Cone and contraction','§3.2、§3.4；数值曲线空间','陈述长度界、局部有限性及收缩的普遍性质。',R`
锥分解|\overline{NE}(X)=\overline{NE}(X)_{K_X+B\ge0}+\sum_j\mathbf R_{\ge0}[C_j]|定理 3.7：X 射影，配对 klt，B 有效有理。C_j 为有理曲线。求和可能无限；非负部分通常不能删去。|Cone decomposition|For a projective effective klt pair, negative extremal rays are generated by rational curves; there may be infinitely many.
极端射线长度|0<-(K_X+B)\cdot C_j\le2\dim X|这是本章对奇异配对使用的界。第一章光滑情形的更强界不能不加说明地代入这里。|Length bound|Use the bound for singular klt pairs, not the stronger smooth bound without additional hypotheses.
远离零面的局部有限性|\overline{NE}(X)=\overline{NE}(X)_{K_X+B+\varepsilon H\ge0}+\sum_{j=1}^{N}\mathbf R_{\ge0}[C_j]|固定充沛 H 与正数 ε，只需有限条负射线。允许射线在 K+B 为零的边界附近聚集，不等于整个锥有限多面体。|Local finiteness|After an ample perturbation only finitely many negative rays remain. Accumulation may occur near the zero boundary.
收缩的曲线判据|f:X\to Y,\quad f_*\mathcal O_X=\mathcal O_Y,\quad f(C)=\mathrm{pt}\iff[C]\in F|对 K+B 负的极端面 F，存在连通纤维的射影收缩。目标正规；曲线判据和层直像条件一起刻画其几何性质。|The contraction|A negative extremal face has a contraction with connected fibres, characterized by the curves it contracts.
线丛下降不是任意数值下降|L\cdot F=0\quad\Longrightarrow\quad L\simeq f^*L_Y|这里 L 为线丛，f 是上述 klt 负面收缩。此下降结论有特定假设，不能对任意连通纤维态射只凭数值平凡就断言成立。|Descent in this setting|Descent applies to line bundles trivial on this negative face; it is not a general claim for every morphism.
曲面上的检验|E^2=-1,\quad K_X\cdot E=-1,\quad\rho(X)-\rho(Y)=1|把极端射线收缩落实到一条例外曲线。讨论：在射影平面，唯一射线给出的是到点的纤维型收缩，不是吹下曲线到曲面。|Test on surfaces|A (-1)-curve gives a birational contraction, while the unique ray of the projective plane contracts to a point.
`);
section('3.4','有理性定理','Rationality theorem','Hilbert 多项式；§3.2','理解 nef 阈值有理性的算术意义。',R`
定义 nef 阈值|r=\max\{t\ge0:H+t(K_X+B)\text{ is nef}\}|设 H 充沛 Cartier，配对 klt 且 K+B 非 nef。取 a 正整数使 a(K+B) Cartier；射线从 nef 锥内部射向边界。|Define the threshold|Start from an ample Cartier class and move in a non-nef adjoint direction; choose a Cartier index a.
有理性和分母界|r=\frac uv,\qquad u,v\in\mathbf Z_{>0},\qquad v\le a(\dim X+1)|定理 3.5 在相应假设下控制既约分母。指数 a 不能遗漏；有理性不是任意两个实数除子确定的边界斜率都具备的性质。|Bound the denominator|The Cartier index enters the bound; this is not a statement about arbitrary real classes.
为什么出现多项式|P(m,n)=\chi\bigl(X,\mathcal O_X(mH+na(K_X+B))\bigr)|Cartier 整数点给出多变量 Euler 特征多项式。证明提纲比较阈值附近的整数点、消失定理和非零截面。|The polynomial input|Use the Euler characteristic polynomial on Cartier lattice points near the threshold, together with vanishing.
零点过多的矛盾|\deg P\le\dim X|证明提纲：若阈值有过大的分母或为无理数，可组织太多整数点迫使相关多项式消失。需保留有效区域条件，不能只凭次数界结束证明。|The arithmetic argument|Too many zeros force a polynomial contradiction, but only after verifying the geometric region where the argument applies.
从有理支持类到态射|L=qH+p(K_X+B),\qquad L\text{ nef Cartier}|把有理阈值清分母，构造支持极端面的整数除子；再核对无基点定理的正性条件，得到收缩。|Clear denominators|Produce an integral supporting divisor and check basepoint-free hypotheses before constructing its morphism.
射影空间检验|X=\mathbf P^n,\quad K_X=-(n+1)H,\quad r=\frac1{n+1}|此例 a=1 且达到分母界。讨论：若用 H 的正整数倍作起点，约分后分母仍受同一上界约束。|Sharp model|Projective space attains the denominator bound with the hyperplane class as starting point.
`);
section('3.5','非消失定理','Nonvanishing theorem','§2.5；Riemann–Roch','理解非消失的归纳结构，避免与完整丰沛性混淆。',R`
常用有效边界版本|H^0(X,mD)\ne0\qquad(m\gg0)|取射影 klt 有效配对，D nef Cartier，并假定 aD-K_X-B nef 且 big。这是定理 3.4 的常用推论，本板不冒充原书带取整的最一般形式。|A useful specialization|Use the effective-klt specialization under nef-and-big adjoint positivity, not the most general rounded-divisor formulation.
为什么 Riemann–Roch 不够|\chi(X,mD)=\sum_i(-1)^ih^i(X,mD)|要从 Euler 特征推出非零截面，必须控制高阶上同调及多项式符号。当 D 的数值维数较小时，最高次项还可能为零。|Why Euler characteristic is not enough|Higher cohomology and polynomial positivity need control, especially when the top self-intersection of D vanishes.
数值维数的分层|\nu(D)=\max\{k:D^k\cdot H^{n-k}>0\}|对 nef D 与充沛 H，数值维数记录实际的正性阶数。按维数归纳时，应区分 D 数值平凡和具有正数值维数的情形。|Numerical dimension|For nef D this measures the order of positivity; the numerically trivial case needs separate treatment.
构造边界的用途|B\ \longmapsto\ B+cM|证明提纲：选取辅助有效除子并调整系数，以产生可控制的中心。每次调整必须追踪 klt 或临界 lc 的变化，不可任意增大边界。|Perturb the boundary carefully|Auxiliary effective divisors create a useful centre; track exactly where klt changes to a limiting lc condition.
降维和延拓的分工|H^0(Z,L_Z)\ne0\quad\longrightarrow\quad H^0(X,L)\ne0|中心上的非消失来自归纳，向 X 延拓来自消失。两步使用不同假设，必须分别说明，而不是把限制映射写成天然满射。|Induction and extension|Induction supplies a section on the centre; vanishing supplies its extension to the ambient variety.
本章闭合逻辑链|\text{nonvanishing}\Rightarrow\text{basepoint-free}\Rightarrow\text{contraction}|返回 §3.2，明确此前引用的输入已获得证明路线。完整技术证明需核对原书的取整与扰动引理；板书中不把提纲称作逐行证明。|Close the logical loop|Return to the earlier basepoint-free argument. Rounding and perturbation lemmas remain explicit technical inputs from the book.
`);
section('3.6','相对版本','Relative versions','§3.2–3.5；相对数值等价','把全局正性改写为底空间上的正性。',R`
只测试被压缩的曲线|D\text{ is }f\text{-nef}\iff D\cdot C\ge0\quad(f(C)=\mathrm{pt})|固定射影态射 f:X→S。相对 nef 比绝对 nef 弱；底空间上的负方向并不由这一条件控制。|Relative nefness|Only curves contracted to a point on the base are tested.
相对曲线空间|N_1(X/S)=\langle[C]:f(C)=\mathrm{pt}\rangle/\equiv|数值等价用 X 上 Cartier 除子的交数定义。相对 Picard 数衡量可收缩的方向，不能用纤维维数代替。|Relative numerical space|Use numerical classes of vertical curves; relative Picard rank is not fibre dimension.
相对无基点结论|f^*f_*\mathcal O_X(mD)\twoheadrightarrow\mathcal O_X(mD)|对相对 nef Cartier D，配对 klt，并有相对 nef 且 big 的 aD-K-B，充分大倍数相对生成。它不要求该层有全局截面。|Relative generation|The evaluation map over the base is surjective for large m; global sections on X are not required.
相对收缩图|X\xrightarrow{g}Y\xrightarrow{h}S,\qquad f=h\circ g|负极端面收缩必须在 S 上。可以在底空间的开集上构造，再利用收缩的唯一性粘合。|Factor over the base|Construct the contraction over S, using local constructions and uniqueness to glue.
加上底空间充沛类|D\ \longmapsto\ D+mf^*A|当底空间也射影时，这常用于把相对问题化为绝对问题。但 m 的存在和所需的全局正性必须验证，不能对任意相对 nef 类直接声称变充沛。|Adding a pullback|A pullback of an ample class can help pass to absolute statements, provided the required positivity is verified.
最简单的相对例子|X=\mathbf P^1\times S,\qquad N_1(X/S)=\mathbf R[\mathbf P^1]|纤维方向形成唯一相对射线，即使 S 本身有复杂曲线锥。讨论班应在此例上区分绝对和相对收缩。|Product example|The relative cone sees only the projective-line fibre, regardless of the cone of the base.
`);
section('3.7','运行极小模型纲领','Running the minimal model program','§3.3、§3.6','辨别终止问题与每一步的存在性。',R`
每一步先检查 nef|K_{X_i}+B_i\text{ nef}\quad\Longrightarrow\quad\text{stop}|起点取射影有理因子化 klt 配对。若邻接类已 nef，则在这一步获得极小模型；这不自动说明其半充沛。|The stopping condition|Nefness stops the program, but does not by itself imply semi-ampleness.
除子型收缩降低 Picard 数|\rho(X_{i+1})=\rho(X_i)-1|负极端射线若收缩一个除子，推前边界并继续。Picard 数下降只能控制除子型步骤，不能证明 flip 序列终止。|Divisorial steps|Picard rank drops by one, controlling divisorial contractions but not flips.
小收缩的困难|\operatorname{codim}\operatorname{Exc}(f_i)\ge2|不能直接把小收缩目标当作下一步的有理因子化模型。flip 用另一侧小模型改变 K+B 的相对符号。|Small contractions|The target need not be the desired Q-factorial model; a flip replaces the small model on the other side.
flip 的符号|-(K_X+B)\text{ is }f\text{-ample},\quad K_{X^+}+B^+\text{ is }f^+\text{-ample}|两侧在收缩目标上双有理同构，边界取严格变换。符号是 flip 定义的一部分，不是说典范除子变成全局充沛。|The sign change|Relative anti-ampleness becomes relative ampleness over the same target.
Mori 纤维空间的出口|\dim Y<\dim X,\quad\rho(X/Y)=1,\quad-(K_X+B)\text{ is }f\text{-ample}|这是另一种终点。极小模型与 Mori 纤维空间的分支取决于几何正性，不能预设所有簇都到达 nef 典范模型。|The fibre-space outcome|A Mori fibre space is a distinct endpoint with relative Picard rank one.
历史范围须标明|\text{existence of flips}\ne\text{termination of flips}|本书为 1998 年的论述。本板给纲领结构，并不把任意维的存在性、终止性和丰沛性都宣布成书内已证结果。|Historical scope|Distinguish existence, termination and abundance, and do not silently assign modern results to the 1998 text.
`);
section('3.8','极小模型与典范模型','Minimal and canonical models','§3.7；双有理公共解消','说明唯一性的层次及负性引理。',R`
极小模型的数值终点|K_X+B\text{ nef}|配合适当的奇点和双有理 discrepancy 条件才构成极小模型的定义。仅凭某个双有理模型 K+B nef，不足以替代所有定义条件。|Minimal models|Nefness is accompanied by singularity and discrepancy requirements in the definition.
典范环与 Proj|R(X,K_X+B)=\bigoplus_{m\ge0}H^0(X,\mathcal O_X(\lfloor m(K_X+B)\rfloor))|有理系数可取 Veronese 子环清分母。有限生成与模型存在需要假设；本式定义一个环，不自行证明有限生成。|The canonical ring|Use a Veronese subring to clear rational denominators; defining the ring does not prove finite generation.
典范模型的唯一性|X_{\mathrm{can}}=\operatorname{Proj}R(X,K_X+B)|在典范模型存在且适用的情形，它由环唯一确定。比较模型时必须使用对应的边界和正确的双有理不变性。|Uniqueness of the canonical model|When a canonical model exists, its Proj description determines it uniquely.
负性引理的安全形式|E\text{ exceptional and }f\text{-nef}\quad\Longrightarrow\quad E\le0|这里 f 为适当双有理态射，E 为有理 Cartier 例外除子。这是负性引理的常用形式；注意结论的符号方向。|Negativity lemma|An exceptional relatively nef Q-Cartier divisor is nonpositive; keep the sign convention consistent.
公共解消比较|p:W\to X,\quad q:W\to X',\quad p^*(K_X+B)-q^*(K_{X'}+B')|比较两侧差的例外部分，用相对 nef 性和负性引理控制。证明提纲由此排除额外除子，获得适用情形的余维一同构。|Compare on a common resolution|Negativity controls exceptional differences of adjoint pullbacks, leading to codimension-one agreement in the minimal-model setting.
唯一性不等于同构|X\dashrightarrow X'\quad\text{may be a flop}|极小模型通常不是唯一的同构类；flop 是最基本的差异来源。第六章在三维中给出存在与连接的严格结果。|Minimal models can differ|Flops explain why uniqueness in codimension one is weaker than uniqueness up to isomorphism.
`);
section('4.1','log canonical 曲面奇点','Log canonical surface singularities','曲面解消；交点矩阵','把 discrepancy 转换成解消曲线的线性方程。',R`
解消上的记号|K_Y=f^*K_X+\sum_i a_iE_i|先取正规有理 Gorenstein 曲面奇点，f 为好解消。带边界时须另加严格变换与拉回，不能继续使用无边界的同一个方程。|Resolution notation|Start with a normal Q-Gorenstein surface; include the boundary terms separately when present.
交点方程|\sum_i a_i(E_i\cdot E_j)=K_Y\cdot E_j|拉回除子与例外曲线交数为零。负定的例外交点矩阵使 discrepancy 系数由这些线性方程唯一确定。|Intersection equations|Pullbacks have zero intersection with exceptional curves; negative definiteness gives uniqueness of the coefficients.
伴随公式的输入|K_Y\cdot E_j=2g(E_j)-2-E_j^2|假定好解消上的分量光滑，便可使用此式。把它代入上一板即可把亏格、自交与奇点类型联系起来。|Adjunction input|For smooth exceptional components, adjunction supplies the right-hand side of the linear system.
一条有理例外曲线|E^2=-r,\quad g(E)=0,\quad a(E)=-1+\frac2r|直接解方程 a(-r)=r-2。此模型展示系数大于负一，但完整分类仍须检查所有例外赋值与解消图的可能性。|One rational component|Solve the discrepancy equation explicitly; the computation is a model, not a replacement for classification.
一条椭圆例外曲线|g(E)=1,\quad E^2<0,\quad a(E)=-1|此时伴随式给出系数负一，解释 lc 与 klt 的分界。进一步吹起光滑点或交层时仍需追踪新的系数。|An elliptic component|The coefficient reaches minus one, illustrating the boundary between lc and klt.
分类的阅读任务|a_i\ge-1\quad\text{versus}\quad a_i>-1|讨论班从交点矩阵逐个验证原书的允许图，不把某一张图的计算当作穷尽性证明。图的存在性与系数判定是两项任务。|Classification tasks|Distinguish checking coefficients on a graph from proving that the classification is exhaustive.
`);
section('4.2','Du Val 奇点','Du Val singularities','§4.1；超曲面局部方程','联系 ADE 方程、解消图与 crepant 性。',R`
典范曲面奇点|K_Y=f^*K_X|在复曲面情形，Du Val 奇点正是典范曲面奇点；极小解消是 crepant。定理 4.20 联系局部方程和解消描述。|Canonical surface singularities|Over the complex numbers, Du Val singularities are the canonical surface singularities, with crepant minimal resolution.
A 系列方程|A_n:\quad xy-z^{n+1}=0\qquad(n\ge1)|极小解消由 n 条负二有理曲线排成链。先算 A₁，再用逐次局部吹起理解链如何增加。|The A series|The minimal resolution of A_n has a chain of n rational (-2)-curves.
D 系列方程|D_n:\quad x^2+y^2z+z^{n-1}=0\qquad(n\ge4)|解消图为 D 型树。分类方程在特征零解析坐标下理解，不能不加条件地套到小正特征。|The D series|The D-type resolution graph is a branched tree; these normal forms are used in characteristic zero.
例外三种|E_6:x^2+y^3+z^4=0;\quad E_7:x^2+y^3+yz^3=0;\quad E_8:x^2+y^3+z^5=0|三种图都是负二曲线组成的 ADE 树。讨论中可比较根格的秩与例外曲线数量，但根格识别不能代替解消证明。|The exceptional types|The exceptional curves form the E-type Dynkin trees; identifying the lattice does not itself construct the resolution.
由负二曲线算典范交数|E_i\simeq\mathbf P^1,\quad E_i^2=-2\quad\Rightarrow\quad K_Y\cdot E_i=0|伴随公式给零，再用负定性得所有 a_i 为零。这解释了为何这些解消是 crepant，而不只是记忆一张分类表。|Compute crepancy|Adjunction gives zero canonical intersection; the negative definite matrix then forces every discrepancy coefficient to vanish.
一个逐步练习|xy=z^2\quad\longrightarrow\quad E\simeq\mathbf P^1,\ E^2=-2|在三个吹起坐标图核对严格变换光滑、例外曲线及法丛次数。此具体计算是 A₁ 例子的完整验证任务。|An explicit exercise|Check the blow-up charts, smoothness and normal degree for the A₁ singularity.
`);
section('4.3','Du Val 同时解消','Simultaneous resolution','§4.2；平坦族与基变换','理解为什么需要有限基变换。',R`
逐纤维解消并不够|\mathcal X\to T,\qquad \widetilde{X_t}\to X_t|为每个纤维单独选极小解消，并不自动给出整个族上的态射；例外曲线的单值性和粘合是额外问题。|Fibrewise is not simultaneous|Separate resolutions need not glue over the parameter space.
最简单的平滑化|xy-z^2=t|中心纤维为 A₁，非零纤维光滑。沿参数原点绕行产生 monodromy，是必须改变底空间的几何提示。|The A₁ smoothing|The central fibre is singular and nearby fibres smooth; monodromy obstructs a naive simultaneous choice.
二重基变换|t=-s^2,\qquad xy=(z-s)(z+s)|分解显示如何选择一个小解消，例如沿理想 (x,z-s) 构造。两个选择互换，对应绕行作用；不能只修改纤维而不修改总空间。|A double base change|Factorization after the cover permits a small-resolution choice; the two choices are interchanged by monodromy.
定理 4.28 的范围|T'\to T\text{ finite},\qquad\mathcal Y\to\mathcal X\times_TT'|对复解析 Du Val 变形芽，适当有限基变换后存在同时极小解消。强调这是原书规定的局部解析设置，不随意推广到任意族。|Scope of the theorem|The simultaneous-resolution statement concerns complex analytic deformations of Du Val germs after a suitable finite base change.
检验同时解消|Y_{t'}\to X_{t'}\quad\text{minimal resolution for every }t'|不仅总空间需要合适，每个纤维限制都必须是目标极小解消。检验平坦性以及纤维是否多出不必要的例外分量。|Check every fibre|The restricted morphism must give the desired minimal resolution on each fibre, not merely resolve the total space.
讨论：选择与唯一性|\text{base change}\ne\text{canonical choice of resolution}|基变换解决存在性，但通常仍有多个选择。后面 flop 的局部模型正利用这种非唯一性。|Choices remain|A finite cover can provide existence without making the resolution canonical; this anticipates flops.
`);
section('4.4','椭圆曲面奇点','Elliptic surface singularities','§4.1；例外循环与上同调','区分椭圆奇点、有理奇点和光滑椭圆曲线。',R`
局部几何亏格|p_g(X,x)=\dim_{\mathbf C}(R^1f_*\mathcal O_Y)_x|这是正规孤立曲面奇点的解消不变量，不是射影曲面的全局几何亏格。必须保留局部点和解消的语境。|Local geometric genus|This resolution invariant of an isolated surface singularity is not the global geometric genus of a projective surface.
有理与椭圆的分界|p_g=0\quad\text{versus}\quad p_g=1|原书椭圆奇点的设置还涉及 Gorenstein 条件。不能把任何出现一条椭圆曲线的解消直接认作同一定义。|The distinction|The book's elliptic-singularity setting includes Gorenstein hypotheses; one cannot classify by seeing an elliptic curve alone.
基本循环|Z=\sum_i m_iE_i>0,\qquad Z\cdot E_i\le0\quad\text{for all }i|在有效非零例外循环中取满足这些条件的最小者。负定性保证构造有控制；可通过不断加入交数为正的分量计算。|The fundamental cycle|Find the minimal positive exceptional cycle with nonpositive intersection against every exceptional component.
循环的算术亏格|p_a(Z)=1+\frac{Z^2+K_Y\cdot Z}{2}|这是循环上的伴随计算，适用于非约化循环，不能把系数 m_i 都删掉再计算。它连接解消图和椭圆性。|Arithmetic genus of a cycle|Multiplicity in the exceptional cycle matters in the adjunction calculation.
简单椭圆模型|E\text{ smooth elliptic},\quad E^2<0,\quad a(E)=-1|一个负法丛的椭圆例外曲线说明 Gorenstein lc 非 klt 的典型行为。与第四章开头的有理例外曲线比较差异。|A simple elliptic model|A negative elliptic exceptional curve is a standard Gorenstein lc but non-klt model.
分类之外还要算层|H^1(Y,\mathcal O_Y)\quad\text{and}\quad H^1(Z,\mathcal O_Z)|局部解消邻域中的上同调与循环的上同调如何联系，需要形式函数等输入。这里列明证明路线，不把图形直观等同于层论证明。|Cohomological input|Relating neighbourhood cohomology to exceptional cycles requires results such as formal functions.
`);
section('4.5','超曲面奇点的变形','Deformations of hypersurface singularities','局部解析代数；偏导理想','从一阶变形到半普遍变形，区分 Milnor 与 Tjurina 数。',R`
一阶变形|f+\varepsilon g=0,\qquad\varepsilon^2=0|坐标变换及乘以单位会改变 g 而不改变同构类。商掉这些平凡方向，得到正确的变形切空间。|First-order deformations|Coordinate changes and multiplication by units generate trivial first-order directions.
Tjurina 代数|T^1\simeq\mathbf C\{x_1,\ldots,x_n\}/(f,\partial_1f,\ldots,\partial_nf)|对孤立超曲面奇点，此商有限维，其维数为 Tjurina 数。注意理想里包含 f，本项不能遗漏。|Tjurina algebra|For an isolated hypersurface singularity the quotient is finite dimensional; the ideal includes f.
Milnor 数不同|\mu=\dim\mathbf C\{x\}/(\partial f),\qquad\tau\le\mu|Milnor 代数没有额外除去 f。准齐次情形 Euler 关系使 f 落入偏导理想，才可得到二者相等。|Milnor versus Tjurina|The Milnor quotient omits f; weighted homogeneity puts f in the Jacobian ideal and gives equality.
半普遍族的候选式|F(x,t)=f(x)+\sum_{i=1}^{\tau}t_i g_i(x)|取 Tjurina 代数的一组基的代表元。原书的半普遍性还需解析变形理论与收敛论证，不能仅凭参数数目相等就宣布证明完毕。|The semiuniversal family|Basis representatives give a candidate family; analytic versality needs a deformation-theoretic proof.
A 型的具体基|f=xy-z^{n+1},\qquad T^1\simeq\mathbf C[z]/(z^n)|偏导消去 x、y 和 z 的 n 次幂，基为一至 z 的 n-1 次幂。因此 τ=n，得到 n 个独立一阶参数。|Compute the A-type example|The Jacobian relations leave the classes of 1 through z to the n-1 as a basis.
讨论：切空间与实际底空间|T_0\operatorname{Def}(X)\quad\ne\quad\operatorname{Def}(X)|在一般变形问题中，切空间维数不能排除障碍与底空间奇点。本节超曲面的良好性质有专门原因，不能泛化到任意奇点。|Tangent space is not the whole base|In general, dimensions of first-order deformations do not rule out obstructions or singular deformation bases.
`);
section('5.1','有理奇点','Rational singularities','解消；高阶直像；对偶','用消失而非局部方程识别有理性。',R`
定义|R^if_*\mathcal O_Y=0\qquad(i>0)|X 正规特征零，f:Y→X 为解消。正规性给出零阶直像；定义还要求所有高阶直像消失。|Definition|For a normal characteristic-zero variety, higher direct images of the structure sheaf vanish on a resolution.
为何不依赖解消|Y\leftarrow W\to Y'|取公共解消，用光滑目标上的消失和 Leray 谱序列比较两侧。这一独立性需要定理，不能仅由双有理等价断言。|Independence|A common resolution and vanishing for morphisms between smooth varieties give independence via Leray.
Cohen–Macaulay 后果|\operatorname{depth}\mathcal O_{X,x}=\dim\mathcal O_{X,x}|有理奇点必为 Cohen–Macaulay，因而对偶层行为较好。反方向不成立：CM 性本身不能保证所有高阶直像为零。|Cohen–Macaulay consequence|Rational singularities are Cohen–Macaulay; the converse is false without additional conditions.
典范层判据|f_*\omega_Y=\omega_X\quad\text{and}\quad X\text{ is CM}|原书用对偶理论把有理性与上述条件联系起来。比较时使用自然映射，并确保对偶层与反身典范层的识别合法。|Canonical-sheaf criterion|Combine Cohen–Macaulayness with the natural canonical-sheaf comparison, using duality.
曲面例子|R^1f_*\mathcal O_Y=0\quad\Longleftrightarrow\quad p_g(X,x)=0|对孤立曲面奇点，这给出第四章局部几何亏格的解释。Du Val 是有理的，简单椭圆奇点不是。|Surface examples|For isolated surface singularities the condition is vanishing local geometric genus; compare Du Val and simple elliptic examples.
证明的输入清单|\text{vanishing}+\text{duality}+\text{Leray}|讨论班分别指出哪一步使用特征零、哪一步使用正规性、哪一步使用 CM 性。避免在证明有理性时先引用只有理奇点才有的结论。|Avoid circularity|Record separately the roles of characteristic zero, normality and Cohen–Macaulayness.
`);
section('5.2','log terminal 奇点与勘误','Log terminal singularities and erratum','§2.3、§5.1','核查 Bertini、覆盖公式、有理性，并完整计算 5.17(2) 的反例。',R`
一般超平面限制|\operatorname{discrep}(X,B)\le\operatorname{discrep}(H,B\vert_H)|这是 Lemma 5.17(1) 的方向，在原书的一般超平面及定义条件下使用。以下反例针对第二项，不能把整条引理统称为错误。|General hyperplane restriction|This is part (1) of Lemma 5.17 under its stated hypotheses; the erratum concerns part (2).
不可直接使用的等式|\operatorname{discrep}(X,B+H)=\min\{0,\operatorname{discrep}(X,B)\}|警告：Lemma 5.17(2) 的此等式一般不成立。Fujino (2004), Remark 10.3 给出反例；2007 年出版版编号为 3.10.6。后六板完整计算。|Incorrect as stated|The displayed equality in Lemma 5.17(2) is false in general. See Fujino (2004), Remark 10.3; published in 2007 as Remark 3.10.6.
余维二的结论|X\text{ terminal}\Rightarrow X\text{ smooth in codimension }2|Corollary 5.18 的超平面论证使用第一项及曲面分类。本处不能因为第二项错误，就自动否定这项推论。|Codimension two|The terminal smoothness statement uses the restriction part and surface classification; the error does not automatically invalidate it.
有限 crepant 覆盖公式|a(E',Y,B_Y)+1=r\bigl(a(E,X,B_X)+1\bigr)|在 K_Y+B_Y 为 K_X+B_X 拉回的有限映射设置下，r 是赋值的分歧指数。变换线性的是 log discrepancy，不是 a 本身。|Finite crepant covers|The ramification index multiplies log discrepancy in the crepant finite-cover setup.
dlt 的有理性| (X,B)\text{ dlt},\quad B\ge0\quad\Longrightarrow\quad X\text{ has rational singularities}|定理 5.22 使用消失及对偶等工具。注意结论说 X 的奇点有理，不是说 X 是有理簇；也不能扩展到任意 lc 配对。|Rational singularities of dlt pairs|The conclusion concerns singularities, not rationality of the variety; it does not extend to all lc pairs.
指数一覆盖的边界|rK_X\text{ Cartier},\qquad K_Y=\pi^*K_X|指数一覆盖是局部构造，要检查正规化与分歧位置。其用途是化为 Gorenstein 问题，并不意味着全局总存在同样形式的无分歧覆盖。|Index-one covers|The local construction reduces to a Gorenstein setting after checking normalization and branching.
勘误一：反例的配对|X=\mathbf P^2,\quad B=L,\quad H\ne L\text{ a general line}|L 与 H 的系数均为一，交于一个横截点 p。原书一般超平面条件满足；错误不是由选择特殊重合直线导致的。|Erratum: the example|Take two distinct transverse lines on the projective plane, both with coefficient one; H is general.
勘误二：原配对的值|\operatorname{discrep}(\mathbf P^2,L)=0|此 discrep 对例外除子取下确界。吹起 L 上一点给出系数零；光滑单分量系数一的配对其余例外 discrepancy 非负。|The original discrepancy|With KM's exceptional-divisor convention, the discrepancy is zero; blowing up a point on L attains it.
勘误三：吹起交点|f:Y=\operatorname{Bl}_p\mathbf P^2\to\mathbf P^2,\quad K_Y=f^*K_X+E|设 L′、H′ 为严格变换。两个光滑分量在 p 的重数都是一，因此各自的总变换都含一个 E。|Blow up the intersection|The canonical divisor adds E, and each boundary component has multiplicity one at the centre.
勘误四：逐项减去边界|\begin{gathered}f^*L=L'+E,\quad f^*H=H'+E\\K_Y+L'+H'=f^*(K_X+L+H)-E\end{gathered}|右边 E 的系数来自一减一减一，故 a(E,X,L+H)=-1。该配对 snc 且所有边界系数为一，lc 性给出下界负一。|Subtract the total transforms|The coefficient is one minus one minus one. Since the snc pair is lc, minus one is also the lower bound.
勘误五：左右两端不等|\operatorname{discrep}(\mathbf P^2,L+H)=-1\ne0=\min\{0,\operatorname{discrep}(\mathbf P^2,L)\}|这已经是完整反例。若改用 A=a+1，则此 E 的 log discrepancy 为零；改记号不能修复原书使用 a 的等式。|The contradiction|The two sides are minus one and zero. Switching to log discrepancy does not repair the stated equality.
勘误六：后续安全用法|a(E)=c-1-\sum b_i,\qquad A(E)=c-\sum b_i|对相容光滑中心直接用吹起公式，或在核对条件后用限制定理与伴随定理。不要把原等式仅加 klt 条件就继续使用；本讨论班不依赖它。|Safe replacements|Compute valuations directly or use correctly qualified restriction and adjunction statements; merely adding klt does not fix this equality.
`);
section('5.3','三维典范与 terminal 奇点','Canonical and terminal threefold singularities','§4.2、§5.2；指数一覆盖','理解一般截面与孤立性各自承担的条件。',R`
compound Du Val 的定义|f(x,y,z)+t\,g(x,y,z,t)=0|局部超曲面的一般截面为 Du Val，称为 cDV。此展示式应在适当局部解析坐标中理解，一张特殊截面不是充分检验。|cDV singularities|A general hyperplane section is Du Val; a single specially chosen section is not enough.
指数一 terminal 三维奇点|X\text{ terminal},\ K_X\text{ Cartier}\quad\Longleftrightarrow\quad X\text{ isolated cDV}|这是三维特征零的局部分类结果之一。孤立性不能删去；cDV 条件单独不足以保证 terminal。|The index-one terminal case|The local threefold statement requires isolated cDV singularities, not merely cDV.
普通双点的例子|xy-zw=0\subset\mathbf A^4|原点为孤立三维超曲面奇点，一般截面为 A₁。该例将用于小解消和 flop，别与二维 A₁ 解消的例外曲线计算混为一谈。|The ordinary double point|This isolated threefold cDV example is the local model for small resolutions and flops.
非孤立 cDV 的警示|xy-z^2=0\subset\mathbf A^4_{x,y,z,t}|这是曲面 A₁ 与直线的乘积，奇点沿一条直线。它典范但不是 terminal，体现孤立条件的重要性。|Why isolated matters|The product of a Du Val surface with a line is canonical but not terminal.
一般截面只能检测部分赋值|\operatorname{discrep}(X,0)\le\operatorname{discrep}(H,0)|引用 Lemma 5.17(1) 时保留不等号方向。一般截面很好，并不允许倒转不等号直接断言三维奇点类型。|Respect the inequality|Good hyperplane sections do not justify reversing the discrepancy inequality.
非指数一的处理|r=\min\{m>0:mK_X\text{ Cartier}\}|先构造局部指数一覆盖，再记录群作用及自由性条件。不能从覆盖的局部方程忘掉群作用而直接宣布原奇点光滑。|Higher index|Analyse the index-one cover together with its group action; the cover alone does not classify the quotient.
`);
section('5.4','伴随的逆命题','Inversion of adjunction','§2.3、§5.2；限制与 different','区分限制边界与 different，明确邻域性。',R`
光滑 Cartier 模型| (K_X+S+B)\vert_S=K_S+B\vert_S|先取 X、S 光滑，S 不在 B 的支撑中，以通常限制理解。一般奇异环境中应使用 different，不能直接写同一个限制符号。|Smooth adjunction first|Ordinary restriction works in the smooth Cartier model; the singular setting requires the different.
正向的伴随| (X,S+B)\text{ plt near }S\Rightarrow(S,B_S)\text{ klt}|S 正规且 B_S 是正确的伴随边界。结论讨论的是 S 附近，不是控制 X 上所有远离 S 的奇点。|Forward adjunction|Use the correct boundary on normal S and retain the neighbourhood qualification.
逆向的困难|(S,B_S)\text{ klt}\Rightarrow(X,S+B)\text{ plt near }S|定理 5.50 在其原书条件下给出逆向。必须控制中心落在 S 中但并非来自 S 的例外赋值，这就是单纯限制公式无法完成的部分。|The inversion problem|The converse must control valuations centred in S, beyond the information visible in the restriction formula.
本讨论的明确适用版本|X,S\text{ smooth},\quad B\ge0,\quad S\not\subset\operatorname{Supp}B|在光滑特征零 Cartier 情形使用上述 klt 与 plt 对应，且 K+S+B 为有理 Cartier。更一般的书内版本逐项核对正规性与边界条件。|A safe working version|Use the smooth characteristic-zero Cartier setting; verify additional assumptions before using the more general book statement.
lc 版本另有条件|\text{lc on }S\quad\Longleftrightarrow\quad\text{lc near }S|原书定理 5.50 的 lc 部分附带额外条件，例如相应的有理 Cartier 边界与 S 的 klt 性。不要用现代更广版本替换而不注明。|The lc version|Keep the additional hypotheses in the book's lc statement rather than silently importing a broader modern theorem.
回看两条直线| (\mathbf P^2,L+H)\text{ lc but not plt at }L\cap H|限制到 L 得到系数一的点，因此不是 klt；这与交点吹起的 discrepancy 负一完全一致，并未使用错误的 5.17(2)。|Revisit the erratum|The coefficient-one restricted point is not klt, agreeing with the blow-up computation without the false equality.
`);
section('5.5','对偶理论','Duality theory','层上同调；CM 层','解释第五章使用的对偶输入，避免把形式类比当证明。',R`
光滑情形的起点|H^i(X,L)^\vee\simeq H^{n-i}(X,\omega_X\otimes L^{-1})|这是光滑射影 n 维簇上线丛的 Serre 对偶。奇异或非局部自由情形不能只把同样的张量表达式机械照搬。|Start with Serre duality|The line-bundle formula on a smooth projective variety does not extend unchanged to every coherent sheaf.
对偶复形的作用|\omega_X^\bullet=f^!\mathbf C|奇异簇上需要整个对偶复形来记录层的各个次数。只有在适当 CM 和纯维条件下，它才集中在一个次数。|Dualizing complexes|The complex retains information in several degrees; concentration requires Cohen–Macaulay hypotheses.
CM 纯维情形|\omega_X^\bullet\simeq\omega_X[n]|这里 X 纯 n 维且 CM。注意平移的符号；它决定最终上同调对偶中 n-i 的出现。|The CM case|For pure-dimensional Cohen–Macaulay X, the dualizing complex is the dualizing sheaf shifted by n.
原书的层论对偶|H^i(X,F)^\vee\simeq H^{n-i}(X,\mathcal Hom(F,\omega_X))|使用定理 5.71 时，X 射影纯 n 维并按原书要求取 CM、纯 n 维的 F。任意 F 的版本需要 Ext，不能漏掉高阶项。|Sheaf duality with hypotheses|For the pure-dimensional CM sheaf setting, Hom suffices; arbitrary coherent sheaves require Ext terms.
与有理奇点连接|Rf_*\mathcal O_Y\simeq\mathcal O_X|对该式应用适当的相对对偶，联系典范层直像与结构层消失。证明必须说明所用的迹映射与自然比较映射。|Back to rational singularities|Duality links the derived structure-sheaf statement to canonical-sheaf comparisons through natural trace maps.
讨论班的核查习惯|\text{properness},\quad\text{pure dimension},\quad\text{CM},\quad\text{shift}|每次引用对偶先写这四项，判断应该使用 Hom 还是 Ext。此习惯能阻止很多看似形式正确的错误同构。|A checklist for duality|Record properness, dimension, CM conditions and shifts before replacing derived duality by a sheaf formula.
`);
section('6.1','flip 与 flop','Flips and flops','§3.7–3.8；相对 Proj','明确相对正性和小双有理模型的区别。',R`
共同的收缩图|X\xrightarrow{f}Z\xleftarrow{f^+}X^+|两侧均为小双有理态射，模型间在余维一同构。flip 和 flop 的区别由典范类及选择除子的相对数值行为决定。|The common diagram|Both sides are small birational models over the same target; their relative positivity distinguishes flip from flop.
flip 改变典范符号|K_X\text{ is }f\text{-anti-ample},\quad K_{X^+}\text{ is }f^+\text{-ample}|这里省略边界仅为说明。对配对必须同时推移边界，用 K+B 检查符号。|The flip sign|For pairs use the adjoint divisor K+B on both sides.
flop 保持典范平凡|K_X\equiv_Z0,\quad -D\text{ is }f\text{-ample},\quad D^+\text{ is }f^+\text{-ample}|D 指定选择方向，因此说 D-flop 比只说 flop 更完整。K 平凡不意味着所有线丛都在收缩曲线上平凡。|Choose a flopping divisor|A chosen D selects the direction while the canonical class remains relatively numerically trivial.
代数存在性问题|X^+=\operatorname{Proj}_Z\bigoplus_{m\ge0}f_*\mathcal O_X(mD)|取足够倍数使式子有意义，并固定对应正性约定。关键是有限生成与新模型的性质，写出 Proj 本身不是存在性证明。|The algebraic construction|Finite generation and the properties of the resulting model must be proved; a formal Proj expression does not settle existence.
普通双点的小解消|xy-zw=0,\qquad\operatorname{Exc}(f)\simeq\mathbf P^1|三维节点有两种标准小解消。例外集是一条曲线、没有例外除子；两模型互换构成最基本的 flop。|The node model|Two small resolutions of the threefold node are related by the basic flop.
法丛检验|N_{\mathbf P^1/X}\simeq\mathcal O(-1)\oplus\mathcal O(-1)|在标准小解消中可由两张局部图算出过渡函数。此模型帮助理解存在的几何，但不代表所有三维 flop 都有相同法丛。|The normal bundle|Compute transition functions in the standard model; not every threefold flop has this normal bundle.
`);
section('6.2','terminal flop','Terminal flops','§5.3、§6.1','阅读三维存在定理与局部模型的关系。',R`
定理 6.14 的范围|\dim X=3,\quad X\text{ terminal},\quad f:X\to Z\text{ a }D\text{-flopping contraction}|在原书的三维 terminal 设置下 D-flop 存在。小收缩、相对正性与有理 Cartier 条件都是输入，不能只给一个任意双有理映射。|The existence theorem|The threefold terminal D-flopping setup includes smallness and relative positivity hypotheses.
相对维数控制|\dim\operatorname{Exc}(f)\le1|三维小收缩没有例外除子，因此例外集为曲线。这是三维证明能利用曲面截面的原因之一。|Exceptional curves|Small threefold contractions have no exceptional divisors; surface sections help analyse the exceptional curves.
截面与 Du Val 输入|S\subset X,\qquad S\to f(S)|证明路线利用合适截面及其解消理论。必须验证截面的选择条件，不能把任意含收缩曲线的曲面都当成 Du Val。|Surface-section input|Choose sections with the required singularities; arbitrary sections through contracted curves do not suffice.
相对有限生成的角色|\mathcal R(D)=\bigoplus_{m\ge0}f_*\mathcal O_X(mD)|有限生成把局部几何转成代数模型，随后检验新模型仍有目标奇点。讨论班应把这两步分开解释。|Finite generation and singularities|Construct the model from the algebra, then verify its singularity properties separately.
crepant 的比较|p^*K_X=q^*K_{X^+}|在公共解消上比较两侧典范拉回，反映 flop 的 crepant 性。证明使用相对数值条件及负性控制，不是余维一同构的直接形式结论。|Crepant comparison|Relative numerical conditions and negativity control the canonical pullbacks on a common resolution.
练习：正性换边|D\cdot C<0,\qquad D^+\cdot C^+>0|在普通双点模型中选具体除子，计算两侧与例外曲线的交数。仅画两条曲线不足以验证其确为所选的 D-flop。|Check the direction|Compute intersection signs in the ordinary-node model to verify the chosen flopping direction.
`);
section('6.3','terminalization 与有理因子化','Terminalization and Q-factorialization','§6.2；负性引理','区分 crepant、small、terminal 和 Q-factorial。',R`
terminalization 的目标|f:Y\to X,\quad Y\text{ terminal},\quad K_Y=f^*K_X|对三维典范奇点，定理 6.23 构造射影 crepant terminalization。它通常会提取 discrepancy 零的除子，不必为小态射。|Terminalization|For canonical threefolds, a projective crepant terminalization can extract discrepancy-zero divisors.
为什么要提取零系数|a(E,X,0)=0|典范允许零，而 terminal 对例外除子要求严格正。将需要的零赋值实现为 Y 上的除子，改变它在新模型中是否例外的地位。|Extract zero discrepancies|A divisor realized on the new model is no longer exceptional over that model, explaining the role of extraction.
有理因子化|\operatorname{WDiv}(Y)\otimes\mathbf Q=\operatorname{CDiv}(Y)\otimes\mathbf Q|Q-factorial 指每个 Weil 除子局部有正倍数 Cartier，不能误解成 Picard 群与除子类群在整数意义下完全相同。|Q-factoriality|Every Weil divisor has a Cartier multiple locally; do not replace this by an integral equality of class groups.
定理 6.25 的小模型|f:Y\to X\text{ small projective},\quad Y\text{ terminal and Q-factorial}|对三维 terminal X 存在这样的有理因子化。小性意味着不引入例外除子，与前面的 terminalization 是不同任务。|Small Q-factorialization|For terminal threefolds, Q-factorialization is small and projective, unlike an extraction in terminalization.
代数与解析不能混用|\text{algebraic Q-factorial}\ \not\Rightarrow\ \text{analytic Q-factorial}|原书 Remark 6.26 提醒局部类别的差异。解析邻域可能出现代数模型上没有的局部除子，陈述时应固定范畴。|Algebraic versus analytic|Q-factoriality can differ between algebraic and analytic local categories; fix the category explicitly.
组合构造的核查|Y\to X'\to X|先 terminalize 再在适当情形有理因子化，逐项记录每一步是否小、是否 crepant、是否射影。不要把所有优点自动传给任意复合。|Track each property|For a composite construction, verify smallness, crepancy and projectivity separately at each step.
`);
section('6.4','典范 flop 与模型连接','Canonical flops','§6.2–6.3；相对 nef','区分有方向的终止与任意反复 flop。',R`
两个极小三维模型|X_1\dashrightarrow X_2,\qquad K_{X_i}\text{ nef over }Z|定理 6.38 讨论射影有理因子化 terminal 三维模型。先用极小模型比较获得余维一同构，才讨论 flop 连接。|Two minimal threefold models|Use the projective Q-factorial terminal setting and establish codimension-one agreement first.
用目标充沛除子指路|D_2\text{ ample},\quad D_1=\text{strict transform of }D_2|选择有效充沛除子控制方向，以其严格变换运行有目的的 flop。方向数据是有限性论证的组成部分。|Use an ample guide|The strict transform of an ample divisor on the target directs the sequence.
有限连接|X_1\dashrightarrow X^{(1)}\dashrightarrow\cdots\dashrightarrow X_2|在定理条件下由有限次适当 flop 连接。此结论不声称任意选择 flop 的策略都有限。|Finite connection|The theorem supplies a finite directed connection, not termination of every arbitrary flopping strategy.
典范底上的设置|f:X\to Z\text{ projective crepant},\quad Z\text{ canonical threefold}|定理 6.43 在固定典范底的 crepant 模型上讨论有效除子 D 所控制的 flop 序列。不要遗漏底空间和 crepant 条件。|A fixed canonical base|Keep the fixed canonical threefold base and the projective crepant hypotheses in the termination statement.
不能左右反复当作反例|X\dashrightarrow X^+\dashrightarrow X|反向 flop 改变方向数据。反复左右切换不满足同一个有效 D 导向的定理条件，因此既不反驳定理，也不证明任意终止。|Reverse flops change the problem|Going back changes the directed-divisor data; it is outside the fixed-direction termination claim.
本章证明地图|\text{local models}\to\text{existence}\to\text{extraction}\to\text{directed termination}|讨论班最后回顾各箭头的输入和维数限制。把三维已证结果与任意维纲领分清，是理解全书结构的关键。|The chapter's proof map|Keep track of dimension and hypotheses when connecting local existence, extraction and directed termination.
`);
section('7.1','半稳定纲领','The semi-stable minimal model program','§3.7；dlt 配对；到曲线的族','固定总空间三维及相对底空间条件。',R`
基本相对设置|X\to Y\to C,\qquad\dim X=3,\quad C\text{ smooth curve}|原书在射影态射、平坦族及 lc 态射条件下讨论半稳定纲领。这里的三维是总空间维数，因此一般纤维为曲面。|The relative setting|The total space is three-dimensional over a smooth curve, so general fibres are surfaces.
加入约化纤维|B+X_c\quad\text{as a boundary}|族的 lc 条件涉及纤维加入边界后的奇点。仅知道每个纤维单独 lc，不能未经检查就替代总空间的配对条件。|Include the fibre|The total-space pair with the fibre added matters, not merely a separate assertion about each fibre.
终止定理 7.7|\text{Q-factorial dlt threefold pair}\quad\Longrightarrow\quad\text{termination in the stated semi-stable setup}|还要保留 X→Y→C、有效边界和原书 lc 族条件。此板不把条件简写成任意三维 dlt flip 都由本定理处理。|The termination statement|Retain the effective boundary and the precise semi-stable family hypotheses of Theorem 7.7.
存在定理 7.8|f:X\to Z\quad\Longrightarrow\quad f^+:X^+\to Z|在相同半稳定框架下，小负收缩有 flip。它解决单步存在，与上一板的整条序列终止是两项不同定理。|Existence of a flip|Single-step existence and termination of a whole sequence are distinct assertions.
纲领的两个终点|K_X+B\text{ nef over }Y\quad\text{or a Mori fibre space over }Y|定理 7.9 组合存在与终止，并保持规定的奇点和族条件。运行时须追踪每个纤维及边界的变换。|The two outcomes|Combine existence and termination while tracking the family and boundary conditions along the program.
讨论：为何底是曲线|X_c\text{ is a Cartier divisor}|光滑曲线底使纤维成为天然的除子边界。高维底上的退化不再由单个纤维除子描述，因此不能直接移用同一证明。|Why a curve base matters|A fibre over a smooth curve is a Cartier divisor, a feature not shared by arbitrary higher-dimensional bases.
`);
section('7.2','半稳定约化','Semi-stable reduction','正规化；对数解消；基变换','处理非约化纤维和交叉结构。',R`
开始时的困难|X_0=\sum_i m_iD_i,\qquad m_i>0|中心纤维可能非约化，也可能支撑不为 snc。解消支撑和消掉重数是不同步骤，不能只画成光滑相交就称半稳定。|Two difficulties|Reduction of multiplicities and normal crossings of the support are separate requirements.
有限基变换|t=s^N|令 N 与出现的重数相容，有助于消除纤维重数。但纤维积通常不是正规，下一步不能省略正规化。|Finite base change|Choose a compatible degree, then normalize the resulting fibre product.
正规化是必需的|X'=\operatorname{Norm}(X\times_C C')|局部方程经基变换可能分裂或产生新奇点；正规化改变总空间及分支数据，不能把它当作无影响的符号步骤。|Normalize explicitly|Base change can split components or introduce new singularities; normalization is a genuine geometric operation.
局部单项式模型|t=x_1^{m_1}\cdots x_r^{m_r}|对数解消把问题化为这类模型，再分析基变换与正规化。讨论班可先算两分量的情况，理解为何用整除条件选择 N。|A local monomial model|Log resolution reduces the local calculation to monomials; start with two components to see the divisibility condition.
定理 7.17 的产物|Y_0\text{ reduced},\quad\operatorname{Supp}(Y_0+B_Y+\operatorname{Exc})\text{ snc}|在原书的有限基变换与射影解消设置下获得半稳定模型。相应的光滑性、约化性和边界交叉性都要一起验收。|The resulting model|Check reduced fibres and normal crossings together with the smoothness and projectivity conditions of the construction.
约化之后还不是极小|K_Y+B_Y\quad\text{need not be nef}|半稳定约化提供好的起点，通常加入很多例外除子。接下来运行相对纲领简化模型，而不是把解消模型直接叫极小模型。|Reduction is not minimality|The resolved model is a starting point; its adjoint divisor need not be nef.
`);
section('7.3','特殊半稳定 flip','Special semi-stable flips','§7.1–7.2；伴随与延拓','理解特殊边界如何支持有限生成证明。',R`
特殊配置| (X,S+B_1)\text{ dlt},\quad\dim X=3|定理 7.32 使用有理因子化总空间、指定的 S 及 B₁。特殊配置不是任意分解边界的方式，而是证明准备后的输入。|The special configuration|Use the Q-factorial threefold dlt setting with the prescribed boundary decomposition of Theorem 7.32.
数值条件|S\text{ Cartier},\quad S\equiv_Z0,\quad S_1\cdot C<0|S 的某一分量与收缩曲线为负，即使整个 S 相对数值平凡。各分量交数可能互相抵消，不应把整除子与分量混淆。|Whole divisor versus components|A relatively trivial divisor can have a component with negative intersection, compensated by other components.
开集上的奇点要求|X\setminus\bigl(S\cup\lfloor B_1\rfloor\bigr)\text{ terminal}|这是特殊定理的额外控制条件之一。报告时不能只写 dlt 三个字就省去对补集的要求。|Control the complement|Terminality on the stated complement is an additional hypothesis, not implied merely by writing dlt.
限制到边界的策略| (K_X+S+B_1)\vert_{S_1}=K_{S_1}+\operatorname{Diff}|证明提纲把三维问题联系到曲面边界上的截面与奇点。different 必须正确计算，不能沿用光滑情形的普通限制。|Restrict using adjunction|Use the different on the boundary surface rather than a naive smooth restriction.
从截面到代数|\mathcal R\to\mathcal R\vert_{S_1}|证明提纲需要控制限制映射及边界上的有限生成，再回到总空间。满射和有限生成的提升都要定理支持，不能从一张图中读出。|Lift from the boundary algebra|Restriction and finite-generation arguments require actual extension results, not just a formal diagram.
此小节得到什么|\text{special configuration}\Rightarrow\text{existence of the flip}|原书先证明特殊情形，再在下一节约化一般半稳定 flip。讨论班把特殊假设逐条列在板上，作为下一节待实现的目标。|What is established|The result is existence in the special configuration, which the next section uses in a reduction argument.
`);
section('7.4','半稳定 flip 的存在','Semi-stable flips','§7.3；相对纲领','追踪化为特殊配置和回到原收缩的过程。',R`
定理 7.42 的任务|f:X\to Z\text{ a semi-stable flipping contraction}|目标是规定半稳定三维框架下的 flip 存在。全程固定底空间和要解决的收缩，不能在辅助修改后忘记原问题。|The task|Construct the flip of the prescribed contraction over the fixed base.
引入辅助模型|\widetilde X\to X\to Z|证明路线先作允许的双有理修改，以获得更可控的边界。记录哪些除子是新提取的，以及它们的 discrepancy。|Auxiliary modifications|Track newly extracted divisors and their discrepancies on the auxiliary model.
安排特殊边界|S\equiv_Z0,\qquad S_1\cdot C<0|这一条件与 §7.3 的输入对应。必须解释纤维边界如何提供它，不能仅因希望应用定理就假定已经满足。|Arrange the special configuration|Explain how the fibre boundary supplies the hypotheses needed for the special-flip theorem.
运行辅助纲领|\widetilde X\dashrightarrow\widetilde X_1\dashrightarrow\cdots|证明提纲中需用已建立的存在和终止结果，注意逻辑不能循环引用当前正要证明的一般 flip 存在。|Avoid circularity|Use only previously established existence and termination results in the auxiliary program.
返回原代数|\bigoplus_{m\ge0}f_*\mathcal O_X(mD)|最终要证明原收缩对应代数有限生成，或构造满足其定义的新模型。辅助模型存在本身不等于原收缩的 flip 已完成。|Return to the original contraction|Identify the original algebra or verify the defining properties of the desired new model.
验收三项性质|\text{smallness};\quad\text{relative ampleness};\quad\text{singularity conditions}|构造后逐项检验小性、正性换边及奇点保持。此六板给证明路线，技术性的边界修改与延拓引理仍须对照原书逐步证明。|Verify the output|Check smallness, the relative sign and singularity conditions; the technical reduction lemmas remain explicit proof inputs.
`);
section('7.5','曲面族的应用','Applications to families of surfaces','§7.2、§7.4；相对典范模型','理解稳定约化中的基变换、存在与唯一性。',R`
从穿孔曲线上的族开始|f^\circ:(X^\circ,B^\circ)\to C^\circ|取满足原书条件的 lc 族，且 K+B 相对充沛。任务是补上缺失的纤维，而不是随便选一个射影闭包。|Start over an open curve|The given lc family has relatively ample adjoint divisor; an arbitrary compactification is not yet the desired extension.
先做基变换与约化|C'\to C,\qquad\widetilde X\to X\times_C C'|有限基变换和半稳定约化产生可运行纲领的模型。更换底空间可能不可避免，不能把定理说成原底上无条件延拓。|Base change may be necessary|Semi-stable reduction after a finite cover supplies an admissible starting model.
相对极小模型阶段|K_Y+B_Y\text{ nef over }C'|用三维半稳定纲领得到相对 nef 模型。其总空间是三维，符合前面定理的维数范围。|The minimal-model stage|The three-dimensional total space allows the semi-stable program to produce a relatively nef adjoint model.
再取典范模型|X^{\mathrm{can}}=\operatorname{Proj}_{C'}\mathcal R(K_Y+B_Y)|需使用该设置下的半充沛或有限生成输入，才能得到相对充沛的典范模型。不能把 nef 与 ample 两步合并。|Then take the canonical model|An additional generation input produces the relatively ample model; nefness alone is not enough.
定理 7.62 的结论| (X',B')\to C'\quad\text{lc family},\quad K_{X'}+B'\text{ relatively ample}|原书规定的族在有限基变换后可延拓为相应的完备 lc 族。陈述中保留边界、族条件和相对充沛性。|The extension statement|After finite base change, the family extends with the specified lc and relative-ampleness properties.
存在与唯一性的分工|\text{reduction and MMP}\quad\text{versus}\quad\text{canonical-model comparison}|存在靠约化与纲领；唯一性比较需固定共同的泛纤维和底空间。不要从构造过程作了很多选择就断言最终典范模型不唯一。|Existence versus uniqueness|Construction uses choices, while comparison of canonical models addresses uniqueness with the generic identification fixed.
`);
section('7.6','进一步结果与全书回顾','Further results and synthesis','前七章的定理依赖','以原书历史范围为界，整理尚需额外输入的命题。',R`
三类问题分开记录|\text{existence};\quad\text{termination};\quad\text{abundance}|flip 存在、序列终止和 nef 邻接除子的半充沛性是不同问题。一个结果不能不加论证地代替另外两个。|Separate three questions|Existence, termination and abundance are distinct problems requiring distinct arguments.
数值与线性正性|D\text{ nef}\quad\not\Rightarrow\quad D\text{ semi-ample in general}|第一章到第三章已经说明需要附加条件；第五章的奇点和第七章的族条件是这些定理能工作的重要部分。|Numerical versus linear positivity|Additional hypotheses bridge nefness to semi-ampleness; singularities and family conditions are essential.
维数在证明中的位置|\dim X=2\to\text{intersection matrices};\quad\dim X=3\to\text{surface sections}|曲面负定矩阵、三维截面和边界降维提供不同工具。把证明推广到高维，必须指出这些工具的替代物在哪里。|Where dimension enters|Intersection matrices and surface sections explain why the surface and threefold arguments are special.
全书的一条主线|\text{rational curves}\to\text{contractions}\to\text{singularities}\to\text{flips}\to\text{families}|不是单向背诵术语：每一箭头都对应一组定理及假设。要求参与者选一个箭头，给出完整的输入、输出与关键计算。|Reconstruct the dependencies|For each arrow, identify its theorem, assumptions and an essential calculation.
再次记住唯一指定的勘误|\text{KM98 Lemma 5.17(2): false in general}|Fujino (2007) 的两条直线反例已在 §5.2 完整计算。后续使用一般超平面、伴随或覆盖公式时，核查没有偷用该错误等式。|Remember the erratum|Audit later hyperplane and adjunction arguments against the explicitly computed counterexample to part (2).
继续阅读的记录方式|\text{statement}+\text{hypotheses}+\text{source year}+\text{proof status}|本讨论按 Kollár–Mori (1998) 组织。进一步文献应单独注明年代和准确范围，避免把书中的历史展望当成今日完整定理清单。|Reading beyond the book|Date later references and record their exact scope; distinguish historical outlook from proved statements.
`);

for(const [title,kind,zh,en] of [
 ['A 系列方程','km-ade','ADE 例外曲线示意 · 每点一条负二曲线','Schematic ADE resolution graphs; each vertex represents a (-2)-curve'],
 ['公共解消比较','km-resolution','公共解消 · 两侧拉回比较','A common resolution for comparing pullbacks'],
 ['勘误三：吹起交点','km-blowup','原理示意 · 严格变换在 E 上分离','Schematic: the strict transforms meet E at distinct points'],
 ['共同的收缩图','km-flop','两个小模型 · 在同一个底上比较','Two small models over one base']]){
 const page=kmBoards.find(p=>p.title===title);page.diagram={kind,title:zh,en};
}

// One student presents one section. Chapters are folders, never playback ranges.
export const kmOutline=[];
for(const chapter of KM_CHAPTERS){
 chapter.start=kmOutline.length;
 for(const part of KM_SECTIONS.filter(s=>s.chapter===chapter.id)){
  part.start=kmOutline.length;part.preparation=part.id==='1.1'?'detailed':'worked-arguments';
  const bodies=organizeBoards(kmBoards.filter(p=>p.section===part.id),{minimum:part.id==='1.1'?24:chapter.id===6?5:[2,4].includes(chapter.id)?4:0});
  const proofs=KM_PROOFS.get(part.id)||[];part.proofs=proofs.map(p=>({title:p.title,...p.proof}));part.boards=bodies.length+proofs.length;
  const common={chapter:chapter.id,section:part.id};
  kmOutline.push({...common,kind:'cover',source:'§ '+part.id,title:'§ '+part.id+' '+part.title,author:'Kollár–Mori (1998)',tex:'',text:'学生读书讨论班 · 本次只讲这一节\n'+(part.preparation==='detailed'?'定义、引理、证明与例子':'含逐步计算与局部证明 · 深层定理注明引用'),en:{source:'§ '+part.id,title:'§ '+part.id+' '+part.en,author:'Kollár–Mori (1998)',text:'Student reading seminar · one section per session\n'+(part.preparation==='detailed'?'Definitions, lemmas, proofs and examples':'Worked arguments; deeper theorems explicitly cited')}});
  kmOutline.push(...bodies,...proofs);
  kmOutline.push({...common,kind:'closing',source:'§ '+part.id+' 讨论结束',title:'谢谢！',author:'',tex:'',text:'',en:{source:'END OF SECTION '+part.id,title:'Thank you!',author:'',text:''}});
  part.end=kmOutline.length-1;part.total=part.end-part.start+1;
 }
 chapter.end=kmOutline.length-1;
}
