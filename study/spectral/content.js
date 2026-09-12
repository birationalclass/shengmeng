import {filteredSubspaces,pageQuotientTex,generalPageDefinition} from './filtered-notation.js?v=92';
import {representativeIn} from './math-notation.js?v=77';
const t=String.raw;
export {filteredSubspaces};
export const lessons=[
 {title:'一个双复形，两种微分',tag:'STARTING DATA',f:[t`\delta_1:K^{p,q}\to K^{p+1,q}`,t`\delta_2:K^{p,q}\to K^{p,q+1}`,t`\delta_1^2=\delta_2^2=0`,t`\delta_1\delta_2+\delta_2\delta_1=0`],text:'每个节点是一个向量空间，不是一个向量。横箭头增加第一指标，纵箭头增加第二指标。两条复合路径互为相反数。',note:'使用方向按钮突出横箭头或纵箭头；悬停时对应的实线箭头会高亮。图是示意窗口，窗口以外不自动取零。',proof:'对任意 a，两条路径给出 δ₂δ₁a 与 δ₁δ₂a。只有它们相加为零，总微分的平方才为零。'},
 {title:'总次数：沿对角线直和',tag:'THE TOTAL COMPLEX',f:[t`C^n:=\operatorname{Tot}^nK=\bigoplus_{i=0}^{n}K^{i,n-i}`,t`D:=\delta_1+\delta_2`,t`D:C^n\longrightarrow C^{n+1}`],text:'第一象限条件使每条总次数对角线只有有限项。选择 n，查看 Cⁿ 的所有直和因子；两种微分都把总次数提高一。',note:'金色对角线表示总次数 i+j=n。箭头的像落在下一条对角线上。',proof:'D²=δ₁²+(δ₁δ₂+δ₂δ₁)+δ₂²=0，因此 (C,D) 是一个上链复形。'},
 {title:'滤过：对角线上的一段',tag:'THE COLUMN FILTRATION',f:[t`F^pC^n:=\bigoplus_{i=p}^{n}K^{i,n-i}`,t`F^{p+1}C^n\subseteq F^pC^n`,t`D(F^pC^n)\subseteq F^pC^{n+1}`],text:'斜虚线框只圈住总次数 n 中第一指标不小于 p 的部分，终点是位置 (n,0) 的项。增加 p 就移去最左边的一项。',note:'p=n+1 时框内没有项，Fⁿ⁺¹Cⁿ=0；p=0 时得到整个 Cⁿ。右端 (n,0) 的项始终显示。',proof:'δ₁ 将 i 变成 i+1；δ₂ 保持 i。因此从 i≥p 出发，两者的像仍有第一指标 ≥p。注意 D 的像在总次数 n+1，未必留在原来的斜框内。'},
 {title:'E₀：先定义商，再识别',tag:'ASSOCIATED GRADED',f:[pageQuotientTex(0),t`F^pC^{p+q}=K^{p,q}\oplus F^{p+1}C^{p+q}`,t`E_0^{p,q}\cong K^{p,q}`],text:'取商消去第一指标大于 p 的分量。这里的自然同构由取第 p 列分量给出，不需要选择补空间。',note:'亮起的单项表示自然识别后的 Kᵖᑫ；淡出的各项仍属于原双复形，并非被删除。这里 q=n−p。',proof:'投影 FᵖCⁿ→Kᵖⁿ⁻ᵖ 是满射，其核恰为 Fᵖ⁺¹Cⁿ。第一同构定理给出所示自然同构。'},
 {title:'E₀',tag:'THE ZEROTH PAGE',f:[pageQuotientTex(0),t`\begin{array}{rcl}d_0^{p,q}:E_0^{p,q}&\longrightarrow&E_0^{p,q+1}\\[.4em]${representativeIn("a",t`K^{p,q}`)}+F^{p+1}C^{p+q}&\longmapsto&Da+F^{p+1}C^{p+q+1}\end{array}`],text:'E₀ 使用各页统一的滤过商定义；它等于关联分次是由 D 保持滤过得到的性质。d₀ 是 D 在商上的诱导微分。',note:'这一条目只讨论 E₀ 与 d₀。',proof:'D 保持 F，因此 d₀([a])=[Da] 良定义。取第 p 列分量的同构将 d₀ 识别为 δ₂。'},
 {title:'E₁',tag:'THE FIRST PAGE',f:[pageQuotientTex(1),t`\begin{array}{rcl}d_1^{p,q}:E_1^{p,q}&\longrightarrow&E_1^{p+1,q}\\[.4em][${representativeIn("a",t`K^{p,q}`)}]_1&\longmapsto&[\delta_1a]_1\end{array}`,t`\delta_2^{p,q}a=0`],text:'E₁ 由滤过商定义，自然同构于逐列 d₀ 上同调；δ₁ 诱导 d₁。',note:'d₁ 的定义域与目标都在 E₁ 层。',proof:'反交换关系保证 δ₁ 将纵向闭元映为闭元，并将纵向边界映为边界。因此 d₁ 良定义。'},
 {title:'一般页：滤过商',tag:'THE FILTERED QUOTIENT',f:[...filteredSubspaces,generalPageDefinition,t`\begin{array}{rcl}d_r^{p,q}:E_r^{p,q}&\longrightarrow&E_r^{p+r,q-r+1}\\[.4em][${representativeIn("a",t`Z_r^{p,q}`)}]_r&\longmapsto&[Da]_r\end{array}`],text:'Eᵣ 定义为原滤过复形中的商空间；D 诱导 dᵣ。',note:'Eᵣ 与前一页上同调自然同构是构造的性质；新的微分 dᵣ 仍需原滤过复形。',proof:'D 将分子与分母分别映入目标分子与分母，从而诱导 dᵣ。构造定理证明 Eᵣ 自然同构于前一页的上同调。'},
 {title:'滤过闭元与边界',tag:'FILTERED SUBSPACES',f:[...filteredSubspaces,t`\begin{gathered}B_s^{p,q}\subseteq F^pC^{p+q}\cap\ker D\subseteq Z_r^{p,q}\\[.7em]Z_{r-1}^{p+1,q-1}+B_{r-1}^{p,q}\subseteq Z_r^{p,q}\end{gathered}`],text:'先定义原滤过复形中的 Z、B，再构造各页。',note:'',proof:''}
];
export const convergence=[
 {title:'逐页上同调、自然过渡与稳定',f:[t`\begin{gathered}E_{r+1}^{p,q}\cong H^{p,q}(E_r,d_r)\\[.5em]=\frac{\ker d_r^{p,q}}{\operatorname{im}d_r^{p-r,q+r-1}}\end{gathered}`,t`\pi_r^{p,q}:\ker d_r^{p,q}\twoheadrightarrow E_{r+1}^{p,q}`,t`r>\max\{p,q+1\}`,t`\begin{gathered}d_r^{p,q}=0,\\ d_r^{p-r,q+r-1}=0,\end{gathered}`,t`E_r^{p,q}\xrightarrow{\sim}E_{r+1}^{p,q}\xrightarrow{\sim}\cdots`],text:'第一象限保证此位置的入射与出射微分同时为零，后续各页自然同构。',note:'',proof:'出射靶的第二指标 q-r+1 为负；入射源的第一指标 p-r 为负。对每个 s≥r，两个微分都为零，故 E_{s+1}^{p,q}≅E_s^{p,q}/0，自然同构于 E_s^{p,q}。'},
 {title:'稳定项 E∞',f:[t`\begin{gathered}E_\infty^{p,q}:=E_{r_0}^{p,q},\\r_0>\max\{p,q+1\}.\end{gathered}`],text:'由前一命题，把这些自然同构的空间共同记作稳定项。',note:'',proof:'选择任意满足界限的 r₀，并使用逐页上同调给出的自然同构进行识别。换一个稳定页只改变所选模型，不改变典范同构意义下的稳定项。'},
 {title:'总上同调的诱导滤过',f:[t`H^n:=H^n(C^\bullet,D)`,t`\begin{gathered}F^pH^n:=\\\operatorname{im}\!\left(H^n(F^pC^\bullet,D)\xrightarrow{H^n(\iota_p)} H^n\right)\end{gathered}`],text:'由各滤过子复形的包含映射，在总上同调上取像。',note:'',proof:'F^pH^n 由具有 F^pC^n 中闭代表元的总上同调类组成。'},
 {title:'收敛',f:[t`E_r^{p,q}\Longrightarrow H^{p+q}`,t`\begin{gathered}E_r^{p,q}\Longrightarrow H^{p+q}(C^\bullet,D)\\[.65em]E_\infty^{p,q}\cong\operatorname{Gr}_F^pH^{p+q}(C^\bullet,D)\end{gathered}`,t`E_{r_0}^{p,q}\Longrightarrow H^{p+q}`,t`d_s=0\quad(\forall s\ge r_0)`],text:'收敛的定义、总复形的收敛性质、起始页记号与退化。',note:'',proof:''}
];

export const initial=[
 {...lessons[0],title:'双复形与总复形',tag:'INITIAL DATA',note:''}
];

export const totalCohomology={title:'先取总复形的上同调',tag:'COHOMOLOGY / THE TARGET',f:[t`Z^n:=\ker(D:C^n\to C^{n+1})`,t`B^n:=\operatorname{im}(D:C^{n-1}\to C^n)\subseteq Z^n`,t`H^n(C,D):=Z^n/B^n`,t`[a]_H=[a+Db]_H\quad(a\in Z^n,\ b\in C^{n-1})`],text:'D²=0 保证每个边界都是闭链，所以这个商空间有定义。Hⁿ 是最终要理解的对象；接下来借助滤过构造 Eᵣ，逐步读出 Hⁿ 的关联分次。',note:'在原坐标图上沿对角线观察总微分。这里的 Hⁿ 是总上同调，不能把它放进某一个 Kᵖᑫ 节点。',proof:'如果 a=Db，那么 Da=D²b=0，故 im D ⊆ ker D。两个闭链给出同一个上同调类，当且仅当它们相差一个边界。'};
