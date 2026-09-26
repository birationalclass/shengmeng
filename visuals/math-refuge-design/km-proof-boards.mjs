// Original worked arguments, not transcriptions of KM98. Each entry states the
// precise proposition it proves and separates any external theorem it uses.
const R=String.raw;
export const KM_PROOFS=new Map();
function proof(section,title,en,scope,input,raw){
 const blocks=raw.trim().split('\n').map(line=>{if(line.split('|').length!==3)throw new Error(section+': '+line);const [text,tex,enText]=line.split('|');if(!enText)throw new Error('Incomplete proof '+section);return {text,tex,enText};});
 KM_PROOFS.set(section,[...(KM_PROOFS.get(section)||[]),{section,chapter:+section.split('.')[0],source:'§ '+section,hideHeading:true,title,layout:'flow',proof:{scope,inputs:input},blocks,tex:blocks.map(b=>b.tex).join('\n'),text:scope+'\n引用输入：'+input,en:{source:'§ '+section,title:en,text:en+'\nWorked argument with the hypotheses shown; KM98 (1998). This does not replace the general theorem when the board treats a special case.'}}]);
}
proof('1.1','固定一点的变形维数计算','Pointed deformation calculation','完整计算：从映射变形下界推出固定一点仍可变形的数值条件。','映射变形维数下界；曲线上向量丛 Riemann–Roch',R`
设定：曲线光滑，映射非恒定|f:C\to X,\quad g=g(C),\quad n=\dim X,\quad E=f^*T_X|Set up the tangent bundle on the curve
秩与次数|\operatorname{rk}E=n,\quad\deg E=-K_X\cdot f_*C=:d|Rank and degree
固定像点至多增加 n 个方程|\dim_{[f]}\operatorname{Hom}(C,X;f(p)=x)\ge\chi(E)-n=d-ng|Impose the point condition
因此|\boxed{d>ng\ \Longrightarrow\ \text{a nonconstant pointed family}}|Conclusion
`);
proof('1.2','分裂后的斜率为什么不下降','Slope under splitting','完整证明：有效循环分裂后至少一个分量保留反典范斜率下界。','有效循环的交数可加性',R`
固定充沛除子，写有效循环分解|C\equiv\sum_i m_iC_i,\quad h_i=H\cdot C_i>0,\quad d_i=-K_X\cdot C_i|Ample degrees are positive
斜率是加权平均|\frac{-K_X\cdot C}{H\cdot C}=\sum_i\frac{m_ih_i}{\sum_jm_jh_j}\frac{d_i}{h_i}|Write the slope as a weighted average
至少一个分量|\frac{-K_X\cdot C_j}{H\cdot C_j}\ge M:=\frac{-K_X\cdot C}{H\cdot C}>0|One component retains the slope
若此分量另有反典范长度界|0<-K_X\cdot C_j\le n+1\ \Longrightarrow\ \boxed{H\cdot C_j\le(n+1)/M}|Apply the separately established length bound
`);
proof('1.3','负曲线确实给出极端射线','A negative curve spans an extremal ray','完整证明：光滑射影曲面上负自交曲线张成闭曲线锥的极端射线。','不同不可约曲线交数非负；充沛类在闭曲线锥非零类上严格为正',R`
构造支持类|E^2<0,\quad H\text{ ample},\quad t=\frac{H\cdot E}{-E^2}>0,\quad D=H+tE|Construct a supporting class
检查每条曲线|D\cdot E=0,\qquad C\ne E\ \Longrightarrow\ D\cdot C\ge H\cdot C>0|Test the irreducible curves
取极限时，分离 E 的系数|z_k=a_k[E]+w_k,\quad D\cdot w_k\ge H\cdot w_k\ge0|Separate the exceptional component
零面只能留下 E|D\cdot z=0\ \Longrightarrow\ H\cdot w_k\to0\ \Longrightarrow\ w_k\to0,\quad\boxed{z\in\mathbf R_{\ge0}[E]}|The zero face is exactly the ray
`);
proof('1.4','负曲线的吹下与终止','Blowing down and termination','完整证明：光滑曲面的负自交且典范负的曲线为负一曲线；连续吹下必终止。','曲面伴随；Castelnuovo 收缩定理（1893）',R`
设曲线既负自交又典范负|E^2<0,\quad K_X\cdot E<0,\quad 2p_a(E)-2=E^2+K_X\cdot E|Apply adjunction to an integral curve
两项均为负整数|p_a(E)\ge0\ \Longrightarrow\ E^2=K_X\cdot E=-1,\quad p_a(E)=0|Both integers must be minus one
正规化与奇点亏格|p_a(E)=g(\widetilde E)+\sum_p\delta_p=0\ \Longrightarrow\ E\simeq\mathbf P^1|Arithmetic genus zero forces smoothness
吹下一次，Picard 数下降一次|X\to X_1,\quad\rho(X_1)=\rho(X)-1\ \Longrightarrow\ \boxed{\text{at most }\rho(X)-1\text{ blow-downs}}|Picard rank bounds the number of blow-downs
`);
proof('1.5','nef 不推出半充沛','Nef need not be semi-ample','完整反例：椭圆曲线上非挠的零次线丛 nef，但任意正次幂都无截面。','曲线上有效除子次数非负；Picard 群',R`
选零次非挠线丛|E\text{ elliptic},\quad L\in\operatorname{Pic}^0(E),\quad L^m\not\simeq\mathcal O_E\ (m>0)|Choose a nontorsion degree-zero bundle
nef 只检验次数|\deg L=0\ \Longrightarrow\ L\text{ nef}|Numerical positivity
假设某正次幂有非零截面|0\ne s\in H^0(E,L^m)\ \Longrightarrow\ D=(s)_0\ge0,\quad\deg D=0|A section would have an effective zero divisor
零除子为空，产生矛盾|D=0\ \Longrightarrow\ L^m\simeq\mathcal O_E\quad\bot\qquad\boxed{L\text{ not semi-ample}}|The section would trivialize that power
`);
proof('2.1','吹起的典范除子系数','Canonical divisor of a blow-up','完整局部计算：光滑余维 c 中心的吹起具有例外系数 c−1。','局部坐标中的典范微分形式',R`
在中心附近取局部坐标|Z=(x_1=\cdots=x_c=0)\subset X,\quad f:Y=\operatorname{Bl}_ZX\to X|Choose coordinates at the smooth centre
一个吹起坐标图|x_1=u_1,\quad x_i=u_1u_i\ (2\le i\le c),\quad x_j=u_j\ (j>c)|Write a blow-up chart
计算最高次微分|f^*(dx_1\wedge\cdots\wedge dx_n)=u_1^{c-1}du_1\wedge\cdots\wedge du_n|Compute the Jacobian factor
读出例外系数|\boxed{K_Y=f^*K_X+(c-1)E}|Read the order along the exceptional divisor
`);
proof('2.2','相对 nef 与绝对 nef','Relative versus absolute nefness','完整例子：相对正性允许底方向为负。','乘积上的除子限制与交数',R`
构造乘积和除子|X=\mathbf P^1\times C,\quad f=p_2,\quad D=p_1^*\mathcal O(1)-p_2^*A,\quad\deg A>0|Set up the product
沿竖直曲线|F=\mathbf P^1\times\{c\},\quad D\cdot F=1|Positive on every fibre
沿水平曲线|S=\{p\}\times C,\quad D\cdot S=-\deg A<0|Negative along the base
比较两种正性|\boxed{D\text{ is }f\text{-ample but not nef on }X}|Relative positivity does not imply absolute positivity
`);
proof('2.3','snc 吹起公式及 dlt 与 plt','An snc blow-up calculation','完整计算：相容光滑中心的 discrepancy；两个系数一分量的交点给出非 plt 配对。','上一节的典范吹起公式；边界总变换',R`
中心包含在边界的相应分量中|B=\sum b_iD_i,\quad f^*D_i=D_i'+E\ (Z\subset D_i),\quad c=\operatorname{codim}Z|Track boundary multiplicities
逐项相减|K_Y+B'=f^*(K_X+B)+\left(c-1-\sum_{Z\subset D_i}b_i\right)E|Subtract total transforms
普通交点取两个系数一分量|c=2,\quad b_1=b_2=1\ \Longrightarrow\ a(E,X,B)=-1|Blow up the crossing
结论与记号|\boxed{\text{snc and dlt}\ \not\Rightarrow\ \text{plt}},\qquad A(E)=a(E)+1=0|Keep discrepancy and log discrepancy distinct
`);
proof('2.4','Kodaira 消失的解析证明','An analytic proof of Kodaira vanishing','证明（以 Bochner–Kodaira 恒等式和 Hodge 代表定理为输入）：光滑复射影簇上充沛线丛的 Kodaira 消失。','Hodge 代表定理；Bochner–Kodaira 恒等式；充沛线丛有正曲率度量',R`
选正曲率度量与调和代表|i\Theta(L)=\omega>0,\quad [\alpha]\in H^q(X,K_X\otimes L),\quad\alpha\in A^{n,q}(X,L)|Take a harmonic representative
Bochner–Kodaira 恒等式|\Delta_{\bar\partial}=\Delta_{\partial}+[i\Theta(L),\Lambda]|Use the analytic identity
在型为 (n,q) 的形式上取内积|0=\langle\Delta_{\bar\partial}\alpha,\alpha\rangle\ge q\lVert\alpha\rVert^2|Curvature is positive in positive cohomological degree
结论|q>0\ \Longrightarrow\ \alpha=0\ \Longrightarrow\ \boxed{H^q(X,K_X\otimes L)=0}|Every harmonic representative vanishes
`);
proof('2.5','边界形式从取整形式推出','Derive the boundary form of vanishing','完整推导：在光滑 snc 情形，把 Kawamata–Viehweg 的取整形式改写为边界形式。','Kawamata–Viehweg 消失（1982）的光滑取整形式',R`
写出全部条件|X\text{ smooth projective},\quad B\text{ snc},\quad0\le b_i<1,\quad D\text{ Cartier}|State the smooth snc setting
令需要取整的正性除子|M=D-K_X-B\quad\text{nef and big}|Identify the positive rational divisor
整系数可提出取整号|\lceil M\rceil=D-K_X+\lceil-B\rceil=D-K_X|Compute the rounding exactly
代入所引用的消失定理|H^q(X,K_X+\lceil M\rceil)=0\ \Longrightarrow\ \boxed{H^q(X,D)=0\ (q>0)}|Conclude the boundary formulation
`);
proof('3.1','半充沛为什么产生收缩','How semi-ampleness gives a contraction','完整证明：半充沛除子所定义态射压缩的曲线，恰为其交数为零的曲线。','全局生成线丛定义态射；Stein 分解；投影公式',R`
取无基点倍数|mL=\phi^*\mathcal O(1),\quad\phi:X\to\mathbf P^N|Choose a generated multiple
取 Stein 分解|X\xrightarrow{f}Y\xrightarrow{g}\phi(X),\quad f_*\mathcal O_X=\mathcal O_Y,\quad A=g^*\mathcal O(1)\text{ ample}|Separate connected fibres from a finite map
逐条计算曲线交数|mL\cdot C=A\cdot f_*C|Use the projection formula
正性判别压缩|\boxed{L\cdot C=0\ \Longleftrightarrow\ f(C)=\mathrm{pt}}|Identify exactly the contracted curves
`);
proof('3.2','截面延拓这一步的完整证明','The section-extension step','完整证明：核层的一阶上同调消失使截面满射；并据此证明曲线上的高次数线丛无基点。一般维数无基点定理仍是引用输入。','长正合列；曲线 Serre 对偶',R`
曲线和任意指定点|C\text{ smooth projective},\quad g=g(C),\quad\deg L\ge2g,\quad p\in C|Fix an arbitrary possible basepoint
写短正合列|0\to L(-p)\to L\to L\vert_p\to0|Use the kernel of evaluation
对偶后是负次数线丛|H^1(C,L(-p))^\vee=H^0(C,K_C\otimes L^{-1}(p))=0|Its degree is at most minus one
评价满射，点任意|H^0(C,L)\twoheadrightarrow L\vert_p\ \Longrightarrow\ \boxed{\operatorname{Bs}\lvert L\rvert=\varnothing}|Eliminate every basepoint
`);
proof('3.3','充沛扰动后的有限性计算','Finiteness after an ample perturbation','证明：由有理曲线长度界和有限维整数格，推出充沛扰动后负射线只有有限条。','锥定理的长度界；Néron–Severi 有限生成；充沛类的序区间估计',R`
设该射线在扰动后仍负|H\text{ ample Cartier},\quad(K_X+B+\varepsilon H)\cdot C<0|Choose a ray that remains negative
用长度界控制充沛次数|\varepsilon H\cdot C<-(K_X+B)\cdot C\le2n\ \Longrightarrow\ H\cdot C<2n/\varepsilon|Bound the ample degree
取 Cartier 数值基并放大 H|m_iH\pm D_i\text{ ample}\ \Longrightarrow\ \lvert D_i\cdot C\rvert\le m_iH\cdot C|Bound every coordinate
有界整数向量只有有限个|\bigl(D_1\cdot C,\ldots,D_\rho\cdot C\bigr)\in\mathbf Z^\rho\ \Longrightarrow\ \boxed{\text{finitely many rays}}|Use the lattice, not compactness alone
`);
proof('3.4','有理支持类满足无基点假设','Verify the supporting divisor hypotheses','完整计算：由有理 nef 阈值构造整数支持除子，并验证无基点定理所需的充沛性。阈值有理性本身在本板引用。','有理性定理；nef 与 ample 的和为 ample',R`
清分母，同时清除 Cartier 指数|r=p/q>0,\quad L=qH+p(K_X+B)\text{ nef Cartier}|Choose an integral supporting divisor
把相邻除子写成正性之和|aL-(K_X+B)=(a-1/p)L+(q/p)H|Rearrange before applying any theorem
第一项 nef，第二项 ample|a>1/p\ \Longrightarrow\ aL-(K_X+B)\text{ ample}|Check the sign of every coefficient
在 klt 假设下应用无基点定理|\boxed{\lvert mL\rvert\text{ basepoint-free for }m\gg0}|Conclude only after checking hypotheses
`);
proof('3.5','曲线上的非消失，含数值平凡分支','Nonvanishing on curves','完整证明：光滑射影曲线上 D nef Cartier 且 aD−K−B 次数正、B 有效时，充分大 m 有非零截面。','曲线 Riemann–Roch；亏格零曲线的 Picard 群',R`
先处理次数正的分支|\deg D>0\ \Longrightarrow\ h^0(C,mD)\ge m\deg D+1-g>0\quad(m\gg0)|Positive degree follows from Riemann–Roch
再处理次数零的分支|\deg D=0,\quad\deg(aD-K_C-B)>0|Separate the numerically trivial case
有效边界迫使亏格为零|2g-2+\deg B<0,\quad\deg B\ge0\ \Longrightarrow\ g=0|Use the adjoint positivity assumption
在射影直线上结束|C\simeq\mathbf P^1,\quad\deg D=0\ \Longrightarrow\ \boxed{\mathcal O_C(D)\simeq\mathcal O_C}|Degree zero is now actually trivial
`);
proof('3.6','相对生成在底空间上是局部性质','Relative generation is local on the base','完整证明：相对评价映射的满射可在底空间开覆盖上检查，因此局部构造可粘合。','拟凝聚层的限制；余核的局部判零',R`
把目标写成评价映射|\epsilon:f^*f_*L\longrightarrow L,\quad Q=\operatorname{coker}\epsilon|Consider the cokernel of evaluation
限制到底空间开集|U\subset S,\quad(f_*L)\vert_U=(f_U)_*(L\vert_{X_U})|Restrict the pushforward to an open set
局部无基点意味着余核局部为零|\epsilon_U\text{ surjective}\ \Longrightarrow\ Q\vert_{X_U}=0|Check surjectivity on the cover
开集覆盖总空间|S=\bigcup U_i\ \Longrightarrow\ X=\bigcup X_{U_i}\ \Longrightarrow\ \boxed{Q=0}|Conclude global relative generation
`);
proof('3.7','为什么 Picard 数不能证明 flip 终止','Why Picard rank does not prove termination of flips','完整论证：除子收缩降低 Picard 数，而两侧相对 Picard 数均为一的 flip 不改变 Picard 数。','相对 Néron–Severi 空间；极端收缩的相对 Picard 数为一',R`
除子收缩每次消去一个方向|f:X\to Y,\quad\rho(X/Y)=1\ \Longrightarrow\ \rho(X)=\rho(Y)+1|Divisorial contractions lower the rank
flip 两侧都是相对秩一|X\to Z\leftarrow X^+,\quad\rho(X/Z)=\rho(X^+/Z)=1|Both small models have relative rank one
因此 flip 不降低 Picard 数|\rho(X)=\rho(Z)+1=\rho(X^+)|The numerical count stays unchanged
只能得出除子步数的界|\boxed{\#\{\text{divisorial steps}\}\le\rho(X)-1}\quad\text{not a bound on flips}|Identify exactly what the argument proves
`);
proof('3.8','典范模型的 Proj 唯一性','Uniqueness from the section ring','完整证明：在共同解消上典范除子仅差有效例外项时，典范环相同；有限生成时其 Proj 相同。','正常簇上有理函数的余维一延拓；相对 Proj',R`
在共同模型上比较，取足够可除的 m|p:W\to X,\quad K_W=p^*K_X+E,\quad E\ge0\text{ exceptional}|Start with an effective exceptional difference
例外极点不会给底空间增加截面|p_*\mathcal O_W(mE)=\mathcal O_X|Use normality and codimension-one regularity
逐个次数的截面相同|H^0(W,mK_W)=H^0(X,mK_X)|Apply the projection formula
环乘法也相容|R(W,K_W)=R(X,K_X)\ \Longrightarrow\ \boxed{\operatorname{Proj}R\text{ is unique}}|Recover the canonical model from the same ring
`);
proof('4.1','discrepancy 的线性方程','Solve for surface discrepancies','完整计算：光滑解消上由例外交点矩阵求 discrepancy；单条负 r 有理曲线给出 a=−1+2/r。','曲面伴随；拉回除子与例外曲线交数为零',R`
把所有未知系数写出来|K_Y=f^*K_X+\sum_i a_iE_i,\quad M_{ji}=E_i\cdot E_j|Write the discrepancy vector
逐条与例外曲线相交|\sum_iM_{ji}a_i=K_Y\cdot E_j=2p_a(E_j)-2-E_j^2|Use adjunction on every component
单曲线情形直接解方程|E\simeq\mathbf P^1,\quad E^2=-r\ \Longrightarrow\ -ra=r-2|A one-by-one intersection matrix
得到系数|\boxed{a=-1+2/r},\qquad r=2\ \Longrightarrow\ a=0|Recover the crepant case
`);
proof('4.2','负二曲线构型为何 crepant','Why the exceptional configuration is crepant','完整证明：负定的光滑有理负二曲线构型具有零 discrepancy（假设目标为 Q-Gorenstein）。','曲面伴随；例外交点矩阵负定',R`
每个分量的伴随计算|E_i\simeq\mathbf P^1,\quad E_i^2=-2\ \Longrightarrow\ K_Y\cdot E_i=0|Compute the canonical intersections
写出线性方程|K_Y=f^*K_X+\sum a_iE_i\ \Longrightarrow\ M a=0|Convert to the intersection matrix
负定意味着可逆|v\ne0\ \Longrightarrow\ v^tMv<0\ \Longrightarrow\ \ker M=0|Use negative definiteness
所有系数消失|a=0\ \Longrightarrow\ \boxed{K_Y=f^*K_X}|The resolution is crepant
`);
proof('4.3','A₁ 的基变换与同时解消','A simultaneous resolution after a double cover','完整局部构造：对 A₁ 平滑族先作 t=s² 基变换，再由二乘二秩一矩阵构造光滑总空间。','两个仿射坐标图；秩一矩阵的关联簇',R`
先作二次基变换|xy=z^2-t,\quad t=s^2\ \Longrightarrow\ xy=(z-s)(z+s)|Factor after base change
引入射影方向|[u:v]\in\mathbf P^1,\quad xv=(z-s)u,\quad(z+s)v=yu|Write the incidence resolution
在 u 非零的坐标图|u=1,\quad z=s+xv,\quad y=(2s+xv)v\quad\Rightarrow\quad(x,v,s)\text{ free}|The first chart is smooth over the base
另一个坐标图同样光滑|v=1,\quad z=yu-s,\quad x=(yu-2s)u\quad\Rightarrow\quad(y,u,s)\text{ free}|The second chart completes the simultaneous resolution
`);
proof('4.4','简单椭圆例外曲线的系数','The discrepancy of a simple elliptic curve','完整计算：单条光滑椭圆例外曲线且自交负时，其 discrepancy 为 −1。','曲面伴随；Q-Gorenstein 拉回',R`
固定例外曲线和系数|K_Y=f^*K_X+aE,\quad E\text{ smooth elliptic},\quad E^2=-d<0|Set up the single exceptional component
伴随公式右侧为零|0=2g(E)-2=(K_Y+E)\cdot E|Use genus one
拉回项与 E 正交|0=(a+1)E^2=-(a+1)d|Substitute the discrepancy formula
系数唯一确定|\boxed{a=-1},\qquad A(E)=0\quad\Rightarrow\quad\text{not klt}|The exhibited valuation already rules out klt
`);
proof('4.5','推导 Tjurina 商，不只背公式','Derive the Tjurina quotient','完整一阶计算：坐标变换和乘单位产生的平凡变形恰给出理想 (f,∂f)。','模 ε² 的 Taylor 展开',R`
在双数环上写变形|f+\varepsilon g,\qquad\varepsilon^2=0|Work to first order
改变坐标|x_i\mapsto x_i+\varepsilon a_i\ \Longrightarrow\ g\mapsto g+\sum_i a_i\partial_i f|Expand the coordinate change
再乘可逆函数|1+\varepsilon b\ \Longrightarrow\ g\mapsto g+bf|Include changes of the defining equation
商掉恰好这些方向|\boxed{T^1=\mathbf C\{x\}/(f,\partial_1f,\ldots,\partial_nf)}|Take the quotient by the trivial directions
`);
proof('5.1','有理性与解消选择无关','Independence of the resolution','证明：在光滑目标的高阶直像消失为输入时，Leray 给出解消独立性。','光滑目标的双有理结构层消失；Leray 谱序列；公共解消',R`
取公共解消|Y\xleftarrow{p}W\xrightarrow{q}Y',\quad h=fp=f'q|Compare both resolutions through one space
光滑目标上的输入|p_*\mathcal O_W=\mathcal O_Y,\quad R^jp_*\mathcal O_W=0\ (j>0)|State the vanishing input explicitly
Leray 只有零行|R^if_*(R^jp_*\mathcal O_W)\ \Longrightarrow\ R^{i+j}h_*\mathcal O_W|The spectral sequence degenerates
对另一侧重复|\boxed{R^if_*\mathcal O_Y\simeq R^ih_*\mathcal O_W\simeq R^if'_*\mathcal O_{Y'}}|The two definitions give the same sheaves
`);
proof('5.2','有限覆盖公式中的加一从哪里来','Why finite covers multiply log discrepancy','完整局部计算：crepant 有限覆盖下 log discrepancy 乘分歧指数。','正规化后除子赋值的分歧公式；特征零',R`
在赋值对应的模型上比较|\pi:Y'\to Y,\quad\pi^*E=rE',\quad K_{Y'}=\pi^*K_Y+(r-1)E'+\cdots|The ramification term is r minus one
底层配对假设 crepant|K_{X'}+B'_{X'}=\pi_0^*(K_X+B_X)|State the required equality on the base
比较 E′ 的系数|a(E',X',B'_{X'})=r\,a(E,X,B_X)+(r-1)|Pull back the discrepancy and add ramification
整理为线性变换|\boxed{a(E')+1=r(a(E)+1)}|Log discrepancy is the quantity that scales
`);
proof('5.3','普通双点与非孤立 cDV 的差别','Discrepancies of two hypersurface models','完整计算：三维普通双点的点吹起系数为一；A₁ 与直线乘积的解消有系数零。','光滑环境的吹起公式；超曲面伴随；曲面 A₁ 的 crepant 解消',R`
先吹起四维环境中的原点|\pi:\widetilde{\mathbf A^4}\to\mathbf A^4,\quad K_{\widetilde{\mathbf A^4}}=\pi^*K_{\mathbf A^4}+3E|Start in the ambient fourfold
普通双点方程重数为二|X=(xy-zw=0),\quad\pi^*X=\widetilde X+2E|Track the total transform of the hypersurface
用伴随相减|K_{\widetilde X}=f^*K_X+(3-2)E\vert_{\widetilde X}|Adjunction gives discrepancy one
乘积模型却有零系数例外除子|S=(xy-z^2=0),\quad K_{\widetilde S\times\mathbf A^1}=f^*K_{S\times\mathbf A^1}\quad\Rightarrow\quad\boxed{\text{not terminal}}|The product resolution exhibits discrepancy zero
`);
proof('5.4','snc 情形的逆伴随计算','Check inversion in the snc model','完整局部核对：光滑 snc 情形，S 以系数一出现，其余相交边界系数小于一时，交层吹起的例外 discrepancy 严格大于 −1。一般逆伴随另行引用。','相容中心的吹起公式；snc 配对的赋值判据',R`
取光滑横截坐标模型|S=(x_1=0),\quad B=\sum_{i=2}^k b_i(x_i=0),\quad0\le b_i<1|Write the local snc boundary
限制到 S|B_S=\sum_{i=2}^k b_i(x_i=0)\vert_S\quad\Rightarrow\quad(S,B_S)\text{ klt}|The restricted coefficients stay below one
吹起余维 c 的相交中心|a(E)=c-1-1-\sum_{i=2}^k b_i=c-2-\sum_{i=2}^k b_i>-1\quad(k\le c,\ c\ge2)|Compute the exceptional discrepancy
系数一若再多一个，严格号失效|c=k=2,\quad b_2=1\ \Longrightarrow\ \boxed{a(E)=-1}|Recover the crossing-lines counterexample
`);
proof('5.5','从导出对偶到 Serre 指标','Recover the Serre duality indices','完整推导：从纯 n 维 CM 对偶层平移和导出对偶推出线丛的 Serre 对偶式。','导出整体对偶；纯维 CM 的对偶复形集中定理',R`
先写对偶复形及局部自由假设|X\text{ projective CM},\quad\dim X=n,\quad L\text{ invertible},\quad\omega_X^\bullet=\omega_X[n]|Fix the hypotheses and shift
线丛没有高阶局部 Ext|R\mathcal Hom(L,\omega_X[n])=(L^{-1}\otimes\omega_X)[n]|Use local freeness
整体对偶|R\operatorname{Hom}(R\Gamma(L),\mathbf C)\simeq R\Gamma(L^{-1}\otimes\omega_X)[n]|Apply the derived theorem
取负 i 次上同调|\boxed{H^i(X,L)^\vee\simeq H^{n-i}(X,L^{-1}\otimes\omega_X)}|Read the shift carefully
`);
proof('6.1','flip 的模型为什么唯一','Why the flip model is unique','证明：若给定小双有理模型上 D 相对充沛，则该模型由底空间上的截面代数唯一恢复。','正常簇的反身层由余维一决定；相对充沛除子的 Proj 恢复',R`
固定同一个底和除子的严格变换|X\xrightarrow f Z\xleftarrow{f^+}X^+,\quad D^+\text{ is }f^+\text{-ample}|Fix the divisor and the base
小性使余维一资料相同|f_*\mathcal O_X(mD)=f^+_*\mathcal O_{X^+}(mD^+)|Compare reflexive divisorial sheaves
恢复相对充沛模型|X^+\simeq\operatorname{Proj}_Z\bigoplus_{m\ge0}f^+_*\mathcal O_{X^+}(mD^+)|Recover the model from the section algebra
只剩原模型的数据|\boxed{X^+\simeq\operatorname{Proj}_Z\bigoplus_{m\ge0}f_*\mathcal O_X(mD)}|Uniqueness does not itself prove finite generation
`);
proof('6.2','Atiyah 小解消的局部坐标','Local coordinates for the Atiyah resolution','完整构造：普通双点的小解消在两个坐标图中光滑，例外集为一条射影直线。一般 terminal flop 存在定理仍作为输入。','关联簇构造；两个仿射坐标图',R`
把普通双点写成秩一矩阵|Z=(xy-zw=0),\quad M=\begin{pmatrix}x&z\\w&y\end{pmatrix}|Factor the determinant
记录共同的行方向|[u:v]\in\mathbf P^1,\quad xv=zu,\quad wv=yu|Introduce the incidence variety
两个坐标图均为三维仿射空间|u=1:\ (x,w,v),\ z=xv,\ y=wv;\qquad v=1:\ (z,y,u),\ x=zu,\ w=yu|Check smoothness explicitly
例外集的维数|f^{-1}(0)=\mathbf P^1,\quad\operatorname{codim}_Xf^{-1}(0)=2\ \Longrightarrow\ \boxed{f\text{ small}}|A curve, not an exceptional divisor
`);
proof('6.3','小态射的 crepant 性与非因子化','Small crepant maps and factoriality','完整论证：Q-Gorenstein 的小双有理态射 crepant；普通双点的光滑小解消也说明底空间并非 Q-factorial。','典范除子在余维一处比较；投影公式；相对充沛线丛',R`
小性排除了例外除子|f:Y\to X\text{ small},\quad K_X\text{ Q-Cartier}\ \Longrightarrow\ \boxed{K_Y=f^*K_X}|There is no divisorial discrepancy term
再取非平凡射影小解消|C\subset\operatorname{Exc}(f),\quad A\text{ is }f\text{-ample}\ \Longrightarrow\ A\cdot C>0|Choose a relatively ample divisor
若底空间 Q-factorial|D=f_*A,\quad mD\text{ Cartier},\quad f^*(mD)=mA|Strict transform equals pullback because the map is small
投影公式给出矛盾|mA\cdot C=mD\cdot f_*C=0\quad\bot|The exceptional curve detects nonfactoriality
`);
proof('6.4','反复 flop 为什么不是终止反例','Reversing a flop and directed termination','完整解释：flop 的逆变换仍可做，但固定有向除子后不能把同一曲线立刻反向继续。','flop 定义中的相对正负性',R`
固定有方向的除子|X\dashrightarrow X^+,\quad D\cdot C<0,\quad D^+\cdot C^+>0|Fix one divisor throughout the process
逆 flop 所需的方向变了|(-D^+)\cdot C^+<0\quad\text{but}\quad D^+\cdot C^+>0|The reverse step is negative for the opposite divisor
因此不能保持同一个负方向|X\dashrightarrow X^+\dashrightarrow X\quad\text{uses }D\text{ and }-D|Alternating is not a directed program
逻辑结论|\boxed{\text{arbitrary flop sequences}\ne\text{a fixed directed program}}|Do not confuse this distinction with a proof of general termination
`);
proof('7.1','中心纤维不改变竖直曲线上的交数','The central fibre is relatively numerically trivial','完整计算：到曲线的平坦族中，纤维除子为底点拉回，与任何竖直曲线交数为零。','Cartier 纤维；投影公式',R`
在底曲线上取局部参数|f:X\to C,\quad0\in C,\quad X_0=f^*(0)|The scheme-theoretic fibre is a pullback
线丛来自底空间|\mathcal O_X(X_0)=f^*\mathcal O_C(0)|Identify its associated line bundle
对竖直曲线使用投影公式|f(\Gamma)=\mathrm{pt}\ \Longrightarrow\ X_0\cdot\Gamma=(0)\cdot f_*\Gamma=0|Its relative intersection is zero
两种负性在相对锥上一致|\boxed{(K_X+X_0)\cdot\Gamma=K_X\cdot\Gamma}|The boundary still changes singularities even though the intersection is unchanged
`);
proof('7.2','消除纤维重数的局部计算','Remove multiplicity after base change','完整局部模型：对 t=x^m 作 t=s^m 基变换并正规化，得到约化分支。该模型不代替一般半稳定约化定理。','特征零下多项式分解；正规化分离光滑分支',R`
考虑一个有重数的局部分量|t=x^m,\quad m>1|Start with a multiple fibre component
作同阶基变换|t=s^m\ \Longrightarrow\ x^m-s^m=0|Pull back by a ramified cover
在代数闭特征零底域上分解|x^m-s^m=\prod_{\zeta^m=1}(x-\zeta s)|Separate the branches
正规化后的每一支|x=\zeta s\ \Longrightarrow\ \boxed{(s=0)\text{ has multiplicity }1}|Normalization makes this local fibre reduced
`);
proof('7.3','限制代数的核与延拓','The kernel of the restriction map','完整证明：Cartier 边界上的截面限制，其唯一一阶障碍位于核层的 H¹；射影相对版本用 R¹。有限生成的深层输入没有由这一步自动解决。','Cartier 除子的理想层；长正合列',R`
选择 Cartier 的 mD 和边界 S|0\to\mathcal O_X(mD-S)\to\mathcal O_X(mD)\to\mathcal O_S(mD)\to0|Write the exact restriction sequence
推前到收缩底空间|f_*\mathcal O_X(mD)\to f_*\mathcal O_S(mD)\to R^1f_*\mathcal O_X(mD-S)|Locate the obstruction
若该高阶直像已由消失定理证为零|R^1f_*\mathcal O_X(mD-S)=0\ \Longrightarrow\ \boxed{f_*\mathcal O_X(mD)\twoheadrightarrow f_*\mathcal O_S(mD)}|The required vanishing gives extension
逐次数相容，才能组成代数映射|\mathcal R(D)\longrightarrow\mathcal R(D)\vert_S|Keep multiplication compatible; finite generation needs a further argument
`);
proof('7.4','小模型与截面代数不变性','Compare section algebras across small models','完整论证：正常小双有理模型对应的除子截面由同一组余维一赋值不等式刻画。一般半稳定 flip 存在仍需要书中的技术约化与有限生成。','正常簇上的除子层由余维一赋值定义',R`
在同一个函数域中写除子截面|H^0(U,\mathcal O(mD))=\{g\in K(X):\operatorname{div}(g)+mD\ge0\text{ on }U\}\cup\{0\}|Use the valuation description
小变换保留所有素除子|X\dashrightarrow X',\quad P\longleftrightarrow P',\quad\operatorname{ord}_P=\operatorname{ord}_{P'}|Compare the same divisorial valuations
每个次数的条件相同|f_*\mathcal O_X(mD)=f'_*\mathcal O_{X'}(mD')|The divisorial inequalities agree
乘法在共同函数域中相同|\boxed{\mathcal R_X(D)=\mathcal R_{X'}(D')}|Transport finite generation only after it has actually been established
`);
proof('7.5','相对典范模型怎样从公共模型比较','Compare relative canonical models','证明：两个模型若在公共解消上仅有有效例外差，则相对典范代数相同，有限生成后相对 Proj 给出同一模型。此比较条件不能从共同泛纤维直接省略。','正常性；投影公式；相对 Proj',R`
在公共模型上明确比较假设|p_i:W\to X_i,\quad D_W=p_i^*D_i+E_i,\quad E_i\ge0\text{ exceptional}|State the exceptional-difference condition
取足够可除的 m|p_{i*}\mathcal O_W(mD_W)=\mathcal O_{X_i}(mD_i)|Push down the exceptional contribution
再推到同一个底空间 C|f_{1*}\mathcal O_{X_1}(mD_1)=h_*\mathcal O_W(mD_W)=f_{2*}\mathcal O_{X_2}(mD_2)|Compare relative sections in every degree
相对代数相同|\boxed{\operatorname{Proj}_C\mathcal R(D_1)\simeq\operatorname{Proj}_C\mathcal R(D_2)}|Conclude uniqueness under the stated comparison hypotheses
`);
proof('7.6','用零次线丛区分数值信息与截面信息','A final test of numerical versus linear information','完整论证：同一椭圆曲线上平凡线丛和非挠零次线丛数值等价，但其截面环完全不同。','非零截面的有效零除子；零次有效除子为空',R`
取数值等价的两个线丛|L\in\operatorname{Pic}^0(E)\text{ nontorsion},\quad L\equiv\mathcal O_E|Fix the same numerical class
平凡线丛每个次数都有截面|H^0(E,\mathcal O_E^{\otimes m})=\mathbf C\quad(m\ge0)|Compute the first section ring
非挠线丛正次数没有截面|s\ne0\ \Longrightarrow\ (s)_0=0\ \Longrightarrow\ L^m\simeq\mathcal O_E\quad\bot|Rule out sections of positive powers
比较两个环|\boxed{R(E,\mathcal O_E)=\mathbf C[t],\qquad R(E,L)=\mathbf C}|Numerical equivalence does not determine the section ring
`);
