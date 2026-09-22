// A board is a mathematical unit, not one isolated formula from the notebook.
// Numbering follows study/spectral/app.js and reading-pages.js.
import {lessons,convergence,totalCohomology} from '../../study/spectral/content.js';
import {hodgeContent,hodgeTitles} from '../../study/spectral/hodge.js';
import {lerayContent,lerayTitles} from '../../study/spectral/leray.js';
const R=String.raw;
const gather=f=>f.length===1?f[0]:R`\begin{gathered}${f.join(R`\\[.35em]`)}\end{gathered}`;
const page=(section,title,f,text,enTitle,enText)=>({source:`§ ${section}`,title,tex:gather(f),text,en:{title:enTitle,text:enText,source:`§ ${section}`}});
export const outline=[
{kind:'cover',source:'学习讲义',title:'谱序列',author:'Sheng Meng',tex:'',text:'双复形、滤过与收敛\nHodge 与 Leray 谱序列',en:{source:'LECTURE NOTES',title:'Spectral Sequences',author:'Sheng Meng',text:'Double complexes, filtrations and convergence\nHodge and Leray spectral sequences'}},
page('1.1–1.5','双复形',[
 R`K=\{K^{p,q}\},\qquad K^{p,q}=0\quad(p<0\text{ or }q<0)`,
 lessons[0].f.slice(0,2).join(R`\qquad`),lessons[0].f.slice(2).join(R`\qquad`)],
 '设 K 为第一象限双复形。两种微分分别增加一个指标；反交换关系使总微分的平方为零。','Double complex','Let K be a first-quadrant double complex. The differentials raise the two indices; anticommutation makes the total differential square to zero.'),
page('1.6–1.7','总复形',[lessons[1].f[0],R`D=\delta_1+\delta_2:C^n\longrightarrow C^{n+1},\qquad D^2=0`],
 '固定总次数 n，沿对角线取直和。第一象限条件保证每条对角线只有有限项。','Total complex','For each total degree n, sum along the diagonal. The first-quadrant condition makes this a finite direct sum.'),
page('1.8','总上同调',[...totalCohomology.f.slice(0,3)],
 '闭元模去边界得到总上同调。两个闭元表示同一类，当且仅当它们相差一个总边界。','Total cohomology','Total cohomology is cycles modulo boundaries. Two cycles represent the same class exactly when their difference is a total boundary.'),
page('1.9–1.10','列滤过与子复形',lessons[2].f,
 '保留第一指标至少为 p 的分量。横向微分提高第一指标，纵向微分保持它，故 D 保持列滤过。','Column filtration','Retain components with first index at least p. The horizontal differential raises that index and the vertical one preserves it, so D preserves the filtration.'),
page('1.11–1.12','上同调的诱导滤过',[
 R`\iota_p:(F^pC^\bullet,D)\hookrightarrow(C^\bullet,D)`,convergence[2].f[1]],
 '由子复形的包含在上同调上取像。FᵖHⁿ 中的类恰好具有属于 FᵖCⁿ 的闭代表元。','Induced filtration on cohomology','Take the image of the map induced by inclusion. These are precisely the cohomology classes with a closed representative in the filtered subcomplex.'),
page('1.13','关联分次',[
 R`\operatorname{Gr}_F^pC^n:=F^pC^n/F^{p+1}C^n`,R`\operatorname{Gr}_F^pD:[a]\longmapsto[Da]`],
 '对相邻滤过层取商，得到关联分次复形。D 保持滤过，因而商上的微分良好定义。','Associated graded','Quotient adjacent filtration steps. Since D preserves the filtration, it induces a well-defined differential on this quotient.'),
page('1.14–1.16','滤过闭元与边界',lessons[7].f,
 '这些都是原总复形中的子空间。分母的包含关系保证下一步定义的页空间确实是商空间。','Filtered cycles and boundaries','These are subspaces of the original total complex. The denominator inclusion ensures that the page quotient below is well defined.'),
page('2.1','一般页',[lessons[6].f[2]],
 '在原滤过复形中构造 Eᵣ。它记录能将微分推入更深滤过层的代表元，并模去相应闭元与边界。','General page','Construct each page inside the original filtered complex, using representatives whose differential lies deeper in the filtration, modulo the specified cycles and boundaries.'),
page('2.2','页上的微分',[lessons[6].f[3]],
 '总微分 D 诱导 dᵣ，双次数为 (r, 1−r)，总次数提高一。它把分母映入目标分母，故与代表元选择无关。','Page differential','The total differential induces a map of bidegree (r, 1−r). It carries the denominator into the target denominator, so it is independent of the representative.'),
page('2.3–2.4, 2.7','逐页上同调',[lessons[5].f[1],convergence[0].f[0],convergence[0].f[1]],
 '下一页自然同构于本页的上同调。自然映射先定义在闭元上；它不是从整个 Eᵣ 到下一页的任意投影。','Page cohomology','The next page is naturally isomorphic to cohomology of this page. The transition map is defined on cycles, not as a projection from the whole page.'),
page('2.5, 2.10','逐位置稳定',[
 R`r>\max\{p,q+1\}\quad\Longrightarrow\quad d_r^{p,q}=d_r^{p-r,q+r-1}=0`,
 R`E_r^{p,q}\xrightarrow{\sim}E_{r+1}^{p,q}\xrightarrow{\sim}\cdots=:E_\infty^{p,q}`],
 '出射靶的第二指标与入射源的第一指标均为负，故两个微分同时为零。稳定界依赖于位置 (p,q)。','Pointwise stabilization','Both differentials vanish because an index of their source or target is negative. The stabilization bound depends on the position (p,q).'),
page('2.6','第零页',[
 R`E_0^{p,q}=F^pC^{p+q}/F^{p+1}C^{p+q}\cong K^{p,q}`,lessons[4].f[1]],
 '取第 p 列分量给出自然识别。横向微分进入被商掉的部分，因此第零页只保留纵向微分。','Zeroth page','Projection onto column p gives the natural identification. The horizontal differential lands in the quotient denominator, leaving only the vertical differential.'),
page('2.8–2.9','第一象限收敛',[
 R`E_\infty^{p,q}\cong F^pH^{p+q}(C,D)/F^{p+1}H^{p+q}(C,D)`,
 R`E_r^{p,q}\Longrightarrow H^{p+q}(C,D)`],
 '每个总次数上的滤过有限，故谱序列收敛。稳定页识别的是关联分次；收敛本身不指定总上同调的典范直和分裂。','First-quadrant convergence','The filtration is finite in each total degree, so the sequence converges. The stable page identifies the associated graded, without choosing a canonical direct-sum splitting.'),
page('2','退化与单行收敛',[convergence[3].f[3],convergence[3].f[4]],
 '退化要求所有位置的后续微分同时为零。若仅有一行非零，每个总次数只有一个滤过商，从而直接识别目标上同调。','Degeneration and a single row','Degeneration requires all later differentials to vanish at every position. With only one nonzero row, the sole graded piece in each degree identifies the abutment.')
];
const hodgeNotes=[
 ['设 X 为紧复流形。按型分解光滑复值微分形式；系数光滑，不要求全纯。','Let X be a compact complex manifold. Decompose smooth complex-valued forms by type; their coefficients need not be holomorphic.'],
 ['由 d²=0 按双次数分解，得到两个平方零关系与反交换关系，因此总复形就是 de Rham 复形。','Decompose d squared by bidegree to obtain the double-complex identities. The total complex is the de Rham complex.'],
 ['Dolbeault 引理给出第一页的层上同调识别；第一象限收敛定理给出目标 de Rham 上同调。','The Dolbeault lemma identifies page one with sheaf cohomology; first-quadrant convergence identifies the de Rham abutment.'],
 ['Hodge 滤过由纯型分量的列滤过诱导。稳定页给出相邻层的商，此时尚未选择直和分裂。','The Hodge filtration is induced by the column filtration on types. The stable page gives adjacent quotients, before any splitting is chosen.'],
 ['进一步假设 X 为紧 Kähler 流形。∂∂̄-引理使每个 Dolbeault 类具有纯型的 d-闭代表元，故所有后续微分为零。','Assume X is compact Kähler. The dd-bar lemma provides a pure-type d-closed representative for each Dolbeault class, forcing all later differentials to vanish.'],
 ['在满足 ∂∂̄ 条件的双复形中，以总闭代表元定义提升。两个选择之差为总边界，所以提升与选择无关。','Under the dd-bar condition, define lifts using total-closed representatives. Two choices differ by a total boundary, so the lifts are canonical.'],
 ['将上一条的典范提升应用于 Dolbeault 双复形。复共轭交换纯型指标，得到交集公式与 Hodge 对称性。','Apply the canonical lifts to the Dolbeault complex. Complex conjugation exchanges types, yielding the intersection formula and Hodge symmetry.']
];
const lerayNotes=[
 ['设 f 为域上概形的态射，𝓕 为 X 上拟凝聚层；目标是把 X 上的上同调与 Y 上的高阶直像联系起来。','Let f be a morphism of schemes over a field and F a quasi-coherent sheaf. Relate cohomology on X to higher direct images on Y.'],
 ['在全部模层的范畴中取内射分解。后续的直像与截面运算均作用于这个明确选定的复形。','Take an injective resolution in the category of all module sheaves. Direct image and global sections will be applied to this chosen complex.'],
 ['逐项取直像；复形的上同调层就是高阶直像。此时还没有取全局截面。','Take the direct image term by term. Its cohomology sheaves are the higher direct images; global sections have not yet been taken.'],
 ['核与像都在层的范畴中取。微分平方为零保证边界层包含于闭元层，商层因而有定义。','Kernels and images are taken as sheaves. A square-zero differential puts boundaries inside cycles, making the quotient sheaf well defined.'],
 ['分别对边界层和上同调层取内射分解，为逐项拼接 Cartan–Eilenberg 分解准备材料。','Resolve the boundary and cohomology sheaves separately, preparing the termwise Cartan–Eilenberg construction.'],
 ['依次对两条短正合列应用内射版马蹄引理。先拼出闭元层的分解，再拼出原复形各项的分解。','Apply the injective horseshoe lemma twice: first to resolve cycles, then to resolve each term of the original complex.'],
 ['每一行分解原复形的一项；纵向映射与横向微分相容，构成 Cartan–Eilenberg 内射双复形。','Each row resolves one term of the original complex. Compatible vertical maps give a Cartan–Eilenberg injective double complex.'],
 ['逐项取 Y 上的全局截面，得到第一象限双分次对象。下一步再规定两种微分及符号。','Take global sections on Y term by term, producing a first-quadrant bigraded object. Its differentials and signs are specified next.'],
 ['层映射原本交换，纵向微分乘以符号 (−1)ᵖ 后得到反交换关系，从而总微分平方为零。','The sheaf maps commute. Multiplying the vertical differential by the sign makes the two differentials anticommute, so their sum squares to zero.'],
 ['使用与第一节相同的列滤过。先沿纵向取上同调，再沿横向取上同调，依次得到前两页。','Use the column filtration from Section 1. Vertical and then horizontal cohomology produce the first two pages.'],
 ['CE 分解中的相应短正合列分裂，因此截面函子在这些列上保持正合；再取横向上同调得到 E₂。','The relevant sequences in the CE resolution split, so global sections preserve their exactness. Horizontal cohomology then gives page two.'],
 ['换一个方向先取上同调。内射层的直像为松层，对全局截面无高阶上同调，因此总复形计算 X 上的层上同调。','Take cohomology in the other direction. Direct images of injectives are flasque and acyclic for global sections, identifying the total cohomology on X.'],
 ['将第一象限收敛定理与上一条的总上同调识别结合，得到 Leray 收敛；第二页已由前面的构造明确给出。','Combine first-quadrant convergence with the preceding total-cohomology identification to obtain Leray convergence, with the previously identified second page.'],
 ['在讲义给定的特征零、射影双有理设定下，充分正扭曲使高次底空间上同调消失，再结合消失定理推出高阶直像消失。','In the stated characteristic-zero projective birational setting, sufficient twisting kills higher base cohomology; the vanishing theorem then yields vanishing of higher direct images.'],
 ['取具有有理奇点的正规复簇及解消。高阶直像消失使第二页仅剩零行，单行收敛给出所示典范同构。','For a normal complex variety with rational singularities and a resolution, higher direct images vanish. Single-row convergence gives the canonical isomorphism.']
];
for(const [i,tex] of hodgeContent.f.entries())outline.push(page(`3.${i+1}`,hodgeTitles[i][0],[tex],hodgeNotes[i][0],hodgeTitles[i][1],hodgeNotes[i][1]));
for(const [i,tex] of lerayContent.f.entries())outline.push(page(`4.${i+1}`,lerayTitles[i][0],[tex],lerayNotes[i][0],lerayTitles[i][1],lerayNotes[i][1]));
