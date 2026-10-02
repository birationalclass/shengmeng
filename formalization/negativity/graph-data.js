export const statusLabels = {done:'✓ Lean 已验证',conditional:'◐ 条件式证明 · 输入未齐',assumption:'◇ 暂作假设',pending:'○ 待完成目标'};
export const nodes = [
{id:'max',title:'有限系数 · 最大比值',status:'done',x:20,y:60,deps:[],decl:'exists_effective_shift',file:'Numerical.lean',paper:'projective',statement:'存在 e > 0，使 d + e·a 逐项非负，并在某个原负系数位置等于零。',scope:'有限支撑实系数模型。已证明全部有限最大值论证；不要求指标类型本身有限。',inputs:['a 的所有系数非负。','若 dᵢ < 0，则 aᵢ > 0；d 存在负系数。'],steps:[['构造有限负支撑','从 d 的有限支撑筛选 dᵢ < 0 的指标。','let s := d.support.filter (fun i => d i < 0)'],['取得最大比值','在有限非空集合上选取 −dᵢ/aᵢ 的最大值。','s.exists_max_image (fun i => -d i / a i) hs'],['证明逐项非负','负项使用最大值不等式；非负项使用 e > 0 与 aᵢ ≥ 0。','(div_le_iff₀ hai).mp hle'],['找到归零分量','最大比值对应的指标 j 满足 dⱼ + e·aⱼ = 0。','div_mul_cancel₀']]},
{id:'least',title:'最小有效平移量',status:'done',x:278,y:60,deps:['max'],decl:'exists_least_effective_shift',file:'Coefficients.lean',paper:'projective',statement:'对所有 t ≥ 0，d+t·a 有效，当且仅当 e ≤ t。',scope:'强化已验证的系数引理：不仅存在可行 e，而且它是有效平移的阈值。',inputs:['与最大比值引理相同的系数条件。'],steps:[['复用最大比值引理','取得 e、有效性与归零指标 j。','exists_effective_shift d a ha hcover hneg'],['证明必要性','若 d+t·a 有效，用 j 处的等式和 aⱼ > 0 推得 e ≤ t。','nlinarith'],['证明充分性','t ≥ e 且 aᵢ ≥ 0，所以 d+t·a 的每项至少为 d+e·a。','mul_le_mul_of_nonneg_right hle (ha i)']]},
{id:'push',title:'系数推出保持有效',status:'done',x:20,y:175,deps:[],decl:'effective_push',file:'Coefficients.lean',paper:'projective',statement:'给定单射 strict : J → I，取 strict(j) 处的系数定义推出；非负系数仍非负。',scope:'真正实现了有限支撑系数的推出模型。它与概形 cycle 推出的对应还需要几何桥接。',inputs:['strict 是单射，代表底上分量的严格变换。','输入系数向量有效。'],steps:[['定义系数推出','用 Finsupp.comapDomain 沿 strict 读取系数。','birationalPush strict hinj d'],['逐项验证','对每个 j，所需非负性就是 d 在 strict(j) 处的非负性。','exact hd (strict j)']]},
{id:'negative',title:'负系数 ⇒ exceptional',status:'done',x:278,y:175,deps:['push'],decl:'negative_is_exceptional',file:'Coefficients.lean',paper:'projective',statement:'系数推出有效时，任何负系数指标都不在 strict 的像中。',scope:'ExceptionalIndex 的定义是“不在 strict 像中”。尚未把这个定义认同为概形上的 exceptional prime divisor。',inputs:['系数推出有效。','所选系数 dᵢ < 0。'],steps:[['假设不是 exceptional','若 i = strict(j)，其系数等于推出在 j 处的系数。','rintro ⟨j, rfl⟩'],['非负与负矛盾','推出有效给 dᵢ ≥ 0，与给定负系数矛盾。','(not_lt_of_ge (hpush j)) hi']]},
{id:'antiample',title:'E 的存在性',status:'assumption',x:20,y:290,deps:[],paper:'antiample',statement:'在仿射底上构造有效 Cartier 除子 E，使 −E 相对 ample。',scope:'原稿 Lemma 1.1；当前尚未形式化截面、Cartier 除子与相对 ample 的这条构造链。',inputs:['待建设：O(−A)、直接像与仿射底上的非零截面。','当前定理参数中只给定 E 和 hE、hanti；并未证明这样的 E 存在。'],steps:[['选 ample 除子','由 projective 取 f-ample Cartier 除子 A。'],['寻找截面','f∗O(−A) 泛秩为一，仿射底上取非零全局截面 s。'],['定义 E','令 E = −A + div(s)，有效且 −E ∼ A。']]},
{id:'strict',title:'几何严格变换与 cycle 推出',status:'assumption',x:20,y:410,deps:[],paper:'projective',statement:'把 strict 单射、ExceptionalIndex 与实际双有理态射的严格变换、exceptional prime 和 cycle 推出对应起来。',scope:'系数模型已定义；这一几何一致性还没有证明。',inputs:['正规双有理态射在余维一处的性质。','实际 cycle 推出系数与严格变换系数的一致性。'],steps:[['构造严格变换','给底上每个素除子指定唯一的非 exceptional 严格变换。'],['核对推出系数','证明函数域次数和维数条件给出当前的系数推出模型。']]},
{id:'cover',title:'exceptional 点的曲线覆盖',status:'assumption',x:20,y:530,deps:[],paper:'support',statement:'exceptional locus 中的点位于被 f 压缩的完整曲线上。',scope:'需要正规底上的同构判据、正维射影纤维和曲线存在性。当前为显式覆盖假设。',inputs:['Zariski 主定理的相关推论。','正维射影纤维中经过点的曲线。'],steps:[['识别非准有限处','正规底上的 proper birational 映射在准有限处是同构。'],['取纤维内曲线','在正维射影纤维中取经过给定点的曲线。']]},
{id:'intersection',title:'真实交数与正性接口',status:'assumption',x:20,y:650,deps:[],paper:'projective',statement:'把线性泛函解释成 D·C，并证明 nef、ample、有效性给出的交数符号。',scope:'目前的 intersection 是给定的线性映射；没有从 Cartier 除子和曲线定义构造它。',inputs:['−D nef ⇒ D·C ≤ 0；−E ample ⇒ E·C < 0。','有效 B 且 C 不在支撑内 ⇒ B·C ≥ 0。','若还相交 ⇒ B·C > 0。'],steps:[['构造交数','定义 Cartier/R-Cartier 除子在曲线上的次数并证明线性。'],['接通符号','证明相对正性和支撑条件蕴含所需非负或严格负不等式。']]},
{id:'curves',title:'在归零分量中找到曲线',status:'assumption',x:20,y:770,deps:[],paper:'projective',statement:'exceptional 分量 F 在 B 中系数为零时，存在 F 中不被 Supp B 包含的压缩曲线。',scope:'当前用 hcurve 明确表达曲线存在，用 hinter 单独表达交数非负。',inputs:['素分量与支撑、闭点及曲线的几何关系。'],steps:[['选择支撑外的点','取 x ∈ F ∖ Supp B。'],['选择压缩曲线','取 F 中经过 x 的压缩曲线 C，于是 C 不包含在 Supp B 中。']]},
{id:'connected',title:'连通纤维与相交曲线',status:'assumption',x:20,y:890,deps:[],paper:'fiber',statement:'若纤维与支撑相交却不被包含，可找到纤维内与支撑相交但不被其包含的曲线。',scope:'不能只靠一般拓扑连通性断言曲线存在。Stein 分解及射影几何部分尚未接入。',inputs:['正规底上的 proper birational 映射的连通纤维。','连通射影纤维中的曲线存在引理。'],steps:[['连通性','由 Stein 分解得到几何连通纤维。'],['找到跨越支撑的曲线','先找到遇到支撑但不被包含的分量，再在其中取曲线。']]},
{id:'support',title:'支撑包含的条件式证明',status:'conditional',x:278,y:290,deps:['cover','intersection'],decl:'exceptional_subset_support',file:'Interfaces.lean',paper:'support',statement:'由曲线覆盖与交数符号推出 exc ⊆ supp。',scope:'Lean 验证的是集合与实数不等式层的推导；覆盖和交数符号仍是参数。',inputs:['hcover：每个 exceptional 点位于一条测试曲线上。','hanti：测试曲线的 degree < 0。','hnonneg：曲线不包含在 supp 中则 degree ≥ 0。'],steps:[['经过每个点取曲线','对 x ∈ exc，由覆盖取 C 经过 x。','hcover x hx'],['曲线必须在支撑内','否则得到 degree C ≥ 0，与 degree C < 0 矛盾。','(not_lt_of_ge (hnonneg c h)) (hanti c)'],['回到原点','x 位于该曲线，因而位于 supp。','exact hsub hc']]},
{id:'core',title:'数值 negativity 核心',status:'conditional',x:278,y:530,deps:['max','antiample','support','curves','intersection'],decl:'effective_of_curve_tests',file:'Numerical.lean',paper:'projective',statement:'给定 E 的系数与曲线交数条件，反证法推出 D 的所有系数非负。',scope:'所有曲线、线性映射与符号条件均出现在定理参数中。此处的几何依赖边表示这些参数的预期来源。',inputs:['hE、hcover：E 有效，且在 D 的负系数位置严格为正。','hnef、hanti：交数符号。','hcurve：归零的负分量可提供非负交数测试。'],steps:[['反设 D 不有效','调用最大比值引理得到 e、有效平移及归零分量。','exists_effective_shift'],['测试有效平移','由显式曲线假设得到 C，使 (D+eE)·C ≥ 0。','hcurve (D + e • E) j'],['线性展开得到矛盾','线性给 D·C + e(E·C)，而两项之和严格小于零。','simp only [map_add, map_smul, smul_eq_mul] at hc; linarith']]},
{id:'iff',title:'有效 ⇔ 推出有效',status:'conditional',x:536,y:175,deps:['negative','core'],decl:'effective_iff_push_effective',file:'Interfaces.lean',paper:'projective',statement:'在 strict 系数模型与明确的曲线接口下，D 有效当且仅当其推出有效。',scope:'本页主要已验证结果。它不是已完成的概形版 projective negativity lemma。',inputs:['strict 与 hinj；coeff 和 intersection 两个线性接口。','hE、hcover、hnef、hanti。','hcurve：存在避开支撑的测试曲线；hinter：其交数非负。'],steps:[['正向：推出保持有效','逐项应用 effective_push。','exact effective_push strict hinj'],['反向：负系数为 exceptional','用推出有效导出负指标不在 strict 的像中。','negative_is_exceptional strict hinj hpush hi'],['把曲线接口接到数值定理','先用 hcurve 取曲线，再用 hinter 得非负交数，应用数值核心。','effective_of_curve_tests; exact ⟨c, hinter B c hB hc⟩']]},
{id:'projective',title:'真正的 projective 版本 (1)',status:'pending',x:536,y:410,deps:['iff','strict','antiample','intersection','curves','support'],paper:'projective',statement:'对正规簇间 projective birational f 和 −D 相对 nef 的 R-Cartier 除子：D ≥ 0 ⇔ f∗D ≥ 0。',scope:'完整几何陈述尚未成为本项目中的 Lean 定理。',inputs:['需将所有模型接口实例化为实际代数几何对象。'],steps:[['构造几何对象','定义或接入 Cartier 除子、cycle 系数和实际交数。'],['消除琥珀色输入','逐项证明 strict、E、曲线与交数假设。'],['应用条件式定理','实例化已验证的 effective_iff_push_effective。']]},
{id:'fiber',title:'纤维二择一的条件式证明',status:'conditional',x:278,y:770,deps:['connected','intersection'],decl:'fiber_support_dichotomy',file:'Interfaces.lean',paper:'fiber',statement:'纤维与支撑不相交，或者整个纤维包含于支撑。',scope:'集合层的反证推导已验证。曲线存在和严格正交数尚未从几何证明。',inputs:['hcurve：部分相交时存在适当的纤维内曲线。','hpositive：相交但不包含支撑给正 degree。','hnef：纤维内曲线的 degree ≤ 0。'],steps:[['区分相交与否','不相交时直接结束。','by_cases hmeet : (fiber ∩ supp).Nonempty'],['反设不被支撑包含','调用 hcurve 取得相交但不被包含的曲线。','hcurve hmeet hsub'],['正交数与 nef 矛盾','同一条曲线的 degree 既 > 0 又 ≤ 0。','(not_lt_of_ge (hnef c hcf)) (hpositive c hcmeet hcs)']]},
{id:'projective2',title:'真正的纤维支撑结论 (2)',status:'pending',x:536,y:650,deps:['fiber','connected','intersection'],paper:'fiber',statement:'对有效 D，f 的每个纤维要么不遇到 Supp D，要么包含于其中。',scope:'还需把集合模型中的 fiber、supp、curve、degree 解释为实际几何对象。',inputs:['真实纤维、支撑和曲线的接口桥接。'],steps:[['接通几何输入','证明连通纤维中的曲线存在及严格正交数。'],['实例化条件式结论','应用 fiber_support_dichotomy。']]},
{id:'chow',title:'Chow 改造与推拉下降',status:'assumption',x:278,y:930,deps:[],paper:'proper',statement:'用正规化的 Chow 改造转到 projective，并用交数与支撑的推拉公式下降。',scope:'相对 Chow 引理与需要的推拉公式尚未形式化。',inputs:['正规 projective 改造存在性。','π∗π∗D = D（第一个为推出、第二个为拉回）的精确形式。','投影公式、有效性拉回、支撑拉回与纤维满射。'],steps:[['转到射影态射','构造 π : X′ → X，使 f ∘ π projective。'],['应用射影版本','将 D 拉回到 X′，核对 nef 与推出条件。'],['下降结论','用 cycle 推出恒等式和支撑的满射下降返回 X。']]},
{id:'proper',title:'Proper negativity lemma',status:'pending',x:536,y:890,deps:['projective','projective2','chow'],paper:'proper',statement:'完整目标：正规簇间 proper birational 态射的 negativity lemma 及纤维支撑结论。',scope:'完整目标尚未完成。绿色与蓝绿色节点显示已验证的组成部分；琥珀色节点是需要补齐的几何输入。',inputs:['先完成 projective 版本，再完成 Chow 与推拉归约。'],steps:[['射影版本','完成有效性等价及纤维支撑二择一。'],['Chow 归约','把 proper 问题提升到 projective 模型。'],['下降至原簇','通过推出及支撑关系得到最终结论。']]}
];

const find=id=>nodes.find(n=>n.id===id);
Object.assign(find('chow'),{title:'Chow 改造与几何推拉性质',statement:'剩余几何输入：正规 Chow 改造的存在，以及真实除子的投影公式、推拉恒等式和支撑拉回。',scope:'下降的逻辑与集合步骤已分离并验证；此节点仅保留尚未证明的几何性质。'});
Object.assign(find('proper'),{y:1410,deps:['properreduce','fiberdown','chow']});
nodes.push(
{id:'coefflaws',title:'系数推出的复合与核',status:'done',x:20,y:1050,deps:['push'],decl:'push_comp',related:['push_zero_iff_exceptional_support','effective_both_signs_iff_zero','push_embDomain','push_add_exceptional','effective_descends_coefficients'],file:'Descent.lean',paper:'proper',statement:'系数推出可复合；零推出等价于 exceptional 支撑；exceptional 项不改变推出。',scope:'六条系数模型定理已验证。嵌入系数的 section 是模型构造，还不是几何 Cartier 拉回。',inputs:['严格变换的单射。','所有系数有限支撑。'],steps:[['复合与核','逐项读取严格变换系数，证明复合公式与零推出的刻画。'],['推拉与 exceptional 项','嵌入系数后推出返回原值；只加 exceptional 系数不改变推出。'],['有效性下降','复用已验证的推出保持有效性。']]},
{id:'projection',title:'真实曲线的投影公式',status:'assumption',x:20,y:1170,deps:[],paper:'proper',statement:'被改造压缩的曲线拉回交数为零；其余曲线给出非负次数倍的原交数。',scope:'实际交数的投影公式仍待几何形式化；其符号推论已在相邻节点完成。',inputs:['真实的 Cartier 拉回与曲线次数。'],steps:[['分类曲线','区分被改造压缩的曲线与映到曲线的情形。'],['投影公式','分别证明交数为零或次数倍公式。']]},
{id:'nefpull',title:'nef 符号沿拉回传递',status:'conditional',x:278,y:1050,deps:['projection'],decl:'nonpositive_pullback',related:['nonpositive_smul'],file:'Descent.lean',paper:'proper',statement:'投影公式的零值或非负倍数条件推出拉回后的交数仍非正。',scope:'符号推导已验证；实际投影公式仍是明确参数。',inputs:['原交数非正。','拉回交数为零，或原交数的非负倍数。'],steps:[['曲线分情况','压缩曲线使用零交数，其余使用非负倍数。'],['保持符号','非负数乘非正数仍非正。']]},
{id:'effdown',title:'有效性沿推出下降',status:'conditional',x:278,y:1170,deps:['push','chow'],decl:'effective_descends',file:'Descent.lean',paper:'proper',statement:'推出保持有效且 push(pull D)=D 时，拉回有效推出原除子有效。',scope:'下降组合已验证；实际除子的推拉恒等式仍需建立。',inputs:['push(pull D)=D。','推出保持有效性。'],steps:[['推出有效拉回','先应用推出保持有效性。'],['代入恒等式','用 push(pull D)=D 返回原除子。']]},
{id:'setdown',title:'满射下的集合关系下降',status:'done',x:278,y:1290,deps:[],decl:'support_dichotomy_descends',related:['subset_iff_preimage_subset','disjoint_iff_preimage_disjoint','composite_fiber'],file:'Descent.lean',paper:'proper',statement:'任意满射的逆像反映包含与不相交；支撑二择一因此下降。',scope:'纯集合层已完整验证，不需要额外几何假设。',inputs:['映射满射。'],steps:[['取原像','每个底空间点取一个原像，反映集合关系。'],['二择一下降','分别下降不相交和包含。']]},
{id:'properreduce',title:'proper 到 projective 的归约',status:'conditional',x:536,y:1170,deps:['projective','effdown','nefpull','chow'],decl:'negativity_descends',file:'Descent.lean',paper:'proper',statement:'在改造及推拉条件下，射影 negativity 结论推出 proper 的有效性等价。',scope:'归约逻辑已验证。Chow 存在性与几何公式是参数，射影几何定理也仍未完成。',inputs:['推拉恒等式与推出的交换关系。','nef 拉回保持和射影 negativity 结论。'],steps:[['上升','拉回 D 并传递 nef 与底上的有效推出。'],['射影结论','对拉回应用射影 negativity。'],['下降','沿推出恢复 D 的有效性。']]},
{id:'fiberdown',title:'纤维支撑二择一下降',status:'conditional',x:536,y:1290,deps:['setdown','projective2','chow'],decl:'fiber_dichotomy_descends',file:'Descent.lean',paper:'proper',statement:'满射改造上每个复合纤维的支撑二择一，下降到底上每个纤维。',scope:'纤维与集合的归约已验证；支撑等于逆像与射影纤维结论仍需几何证明。',inputs:['改造满射。','上方支撑是下方支撑的逆像。','上方每个纤维满足二择一。'],steps:[['复合纤维','复合纤维等于原纤维的逆像。'],['满射下降','应用已验证的集合二择一下降。']]}
);

Object.assign(nodes.find(n=>n.id==='projection'),{
  deps:['geomcycle'],statement:'需要证明 (π*D)·Γ = D·π_*[Γ]，由此得到 −π*D 的相对 nef 性。',
  scope:'完整的几何交数等式尚待形式化。真实 Scheme-cycle 推出的基础部分已验证；nef 符号推论也已验证。',
  inputs:['π:X′→X 是 proper birational，f:X→Y，g=f∘π。D 为 X 上的 R-Cartier 除子。','Γ⊂X′ 是满足 g(Γ) 为点的完整整曲线。','需建立 Cartier 拉回与曲线交数的投影公式，而不只是给交数一个线性接口。'],
  steps:[['若 π 压缩 Γ','π_*[Γ]=0，需证明 (π*D)·Γ=0。'],['若 π(Γ)=C 是曲线','令 r=[k(Γ):k(C)]>0，需证明 (π*D)·Γ=r(D·C)。'],['推出 nef 拉回','此时 C 被 f 压缩，D·C≤0，所以 (π*D)·Γ≤0。']]
});
nodes.find(n=>n.id==='projection').precise={
  zh:{setup:'π:X′→X，f:X→Y，g=f∘π；D 是 X 上的 R-Cartier 除子。Γ⊂X′ 是被 g 压缩的完整整曲线。',zero:'若 π(Γ) 是点：',curve:'若 π(Γ)=C 是曲线：',degree:'r=[k(Γ):k(C)]>0。这里 r 是函数域扩张次数。',use:'因为 g 压缩 Γ，曲线 C 也被 f 压缩。−D 为 f-nef 意味着 D·C≤0，因此以上两种情形都给 (π*D)·Γ≤0，即 −π*D 为 g-nef。',gap:'已证明 cycle 推出的零值／次数权重性质。还需构造实际 Cartier 拉回和曲线交数，并证明上面的等式。'},
  en:{setup:'π:X′→X, f:X→Y, g=f∘π. D is an R-Cartier divisor on X. Γ⊂X′ is a proper integral curve contracted by g.',zero:'If π(Γ) is a point:',curve:'If π(Γ)=C is a curve:',degree:'r=[k(Γ):k(C)]>0 is the function-field extension degree.',use:'Since g contracts Γ, f contracts C. Relative nefness of −D gives D·C≤0. Both cases yield (π*D)·Γ≤0, so −π*D is g-nef.',gap:'The zero / degree weights in actual scheme-cycle pushforward are proved. Actual Cartier pullback and curve intersection, and the displayed identity, remain to be constructed and proved.'}
};
nodes.push({id:'geomcycle',title:'真实 Scheme-cycle 的推出',status:'done',x:20,y:1290,deps:[],decl:'scheme_cycle_map_effective',related:['scheme_mapCoeff_zero_of_drop','scheme_mapCoeff_of_same_weight','scheme_cycle_map_zero_of_drop'],file:'GeometricCycles.lean',paper:'proper',statement:'直接对 mathlib 的 AlgebraicCycle 与 Scheme 态射，证明推出保持有效，以及降维为零、同维按剩余域次数计重。',scope:'这四条结果使用真实 Scheme-cycle API。它们还不包含 Cartier 拉回和曲线交数的完整射影公式。',inputs:['Scheme 态射 f 的 QuasiCompact 条件。','权重函数 wx,wy 指定维数／余维数。','cycle 的系数为实数；有效性为逐点非负。'],steps:[['推出保持有效','每项都是非负系数乘自然数次数权重，再取有限和。'],['降维为零','wx(x)≠wy(f(x)) 时，mapCoeff 的定义给权重 0。'],['同维按次数计重','wx(x)=wy(f(x)) 时，权重等于 f.residueDegree(x)。']]});

// Projection input refinement: distinguish proved cycle algebra from actual Cartier geometry.
nodes.find(n=>n.id==='geomcycle').related.push('scheme_cycle_map_single','scheme_curve_push_of_same_weight','scheme_curve_push_of_drop');
nodes.find(n=>n.id==='geomcycle').scope='使用真实 Scheme-cycle API，已证明有效性与单分量推出的零值／次数倍公式。权重函数仍须由实际维数选定；不包含 Cartier 交数兼容性。';
nodes.push({id:'realspan',title:'射影公式的实线性延伸',status:'done',x:20,y:1450,deps:[],decl:'projection_formula_on_real_span',file:'Projection.lean',paper:'proper',statement:'两个实线性映射在 Cartier 生成元上相等，则在其张成空间上相等。',scope:'实线性代数步骤已验证。实际 Cartier 生成元、拉回和交数映射仍需几何构造。',inputs:['拉回及两侧交数是实线性映射。','D 属于 Cartier 生成元的实线性张成。','在 Cartier 生成元上已建立射影公式。'],steps:[['比较线性映射','把两侧视为同一实向量空间到实数的线性映射。'],['在生成元上验证','Cartier 生成元上的等式是明确输入。'],['延伸','LinearMap.eqOn_span 将等式延伸到每个有限实线性组合。']]});
nodes.find(n=>n.id==='projection').deps=['geomcycle','realspan'];
nodes.find(n=>n.id==='projection').precise.zh.gap='单曲线 cycle 的零值／次数倍推出，以及从 Cartier 生成元到实线性张成的延伸均已证明。唯一尚未建立的交数兼容性是：对 Cartier 生成元 A，up(single x 1)=down(map π wx wy (single x 1))。这里 up 是 π*A 的真实交数，down 是 A 的真实交数；这两个映射仍需几何构造。';
nodes.find(n=>n.id==='projection').precise.en.gap='Single-curve cycle pushforward and extension from Cartier generators to their real span are proved. The remaining intersection compatibility is up(single x 1)=down(map π wx wy (single x 1)) for each Cartier generator A. Here up must be actual intersection with π*A and down actual intersection with A; these geometric maps still need construction.';
nodes.push({id:'projectioncases',title:'由 cycle 推出交数两种情形',status:'conditional',x:278,y:1450,deps:['projection','geomcycle'],decl:'projection_cases_from_cycle_push',file:'Projection.lean',paper:'proper',statement:'给定真实交数与 cycle 推出的兼容等式，推导压缩曲线交数为零、同维曲线交数为剩余域次数倍。',scope:'两种情形由实际 AlgebraicCycle.map 推导，已不再单独假设一个零值／倍数的析取。交数兼容性仍是 hcompat 参数。',inputs:['up/down 是 cycle 上的交数加法映射。','hcompat：up([Γ])=down(π_*[Γ])。','权重对应实际曲线及其像的维数。'],steps:[['cycle 推出','直接使用真实 Scheme-cycle 的单分量推出公式。'],['交数加法性','交数加法映射把自然数倍 cycle 变为次数倍交数。'],['得到两种情形','权重下降给零，同权重给 residueDegree 倍数。']]});
Object.assign(nodes.find(n=>n.id==='nefpull'),{deps:['projectioncases'],decl:'nonpositive_pullback_from_cycle_push',related:['nonpositive_pullback','nonpositive_smul'],file:'Projection.lean',statement:'从真实 cycle 推出与交数兼容性推导非正交数沿拉回保持。',scope:'已验证实际 Scheme-cycle API 上的条件式符号传递。原有析取输入已由 cycle 两种情形取代；交数兼容性和像曲线可测试性仍为参数。',inputs:['hcompat：上方交数等于下方对推出 cycle 的交数。','同维像曲线是底上允许测试的压缩曲线。','底上测试曲线交数非正。']});
nodes.push({id:'pushpull',title:'真实除子的推拉恒等式',status:'assumption',x:20,y:1570,deps:[],paper:'proper',statement:'π 为正规簇间 proper birational 态射，D 为 R-Cartier 除子，需要建立 π_*(π*D)=D。',scope:'尚需构造真实 Cartier 拉回及其 underlying Weil cycle，并证明在每个底上素除子处的推出系数恢复原系数。',inputs:['pull D 是实际 Cartier 拉回，不能仅选取任意有效 cycle。','在非例外严格变换上的系数与剩余域次数恢复 D。','例外分量因维数下降而不贡献推出。'],steps:[['核对严格变换','每个底上素除子的非例外严格变换给原系数。'],['核对例外分量','维数下降的例外分量推出为零。'],['cycle 等式','逐素除子比较系数，证明 π_*(π*D)=D。']]});
Object.assign(nodes.find(n=>n.id==='effdown'),{deps:['geomcycle','pushpull'],decl:'scheme_effective_descends',related:['effective_descends'],file:'Projection.lean',statement:'真实 Scheme-cycle 的推出已保持有效；若 π_*(π*D)=D 且 π*D 有效，则 D 有效。',scope:'有效性下降已接入实际 AlgebraicCycle.map。尚待几何证明的 map-property 输入只有 hleft，即实际 Cartier 拉回的推拉恒等式；hlifted 是应用此定理时的已知条件。',inputs:['hleft：AlgebraicCycle.map π wx wy lifted = D，其中 lifted 是 π*D 的 underlying cycle。','hlifted：CycleEffective lifted，即拉回除子已有效。','推出保持有效已由 scheme_cycle_map_effective 证明，不再假设。'],steps:[['使用已证明的推出有效性','将有效 lifted 经真实 AlgebraicCycle.map 推出，得到有效的 π_*lifted。'],['代入唯一待补恒等式','用 hleft：π_*lifted=D，得到 D 有效。']]});

// Standard codimension-one proof: keep its geometric construction separate from the checked local algebra.
nodes.push({id:'localorder',title:'DVR 局部系数与同构',status:'done',x:20,y:1680,deps:[],decl:'dvr_order_ringEquiv',related:['dvr_fraction_order_well_defined','dvr_fraction_order_ringEquiv','scheme_stalk_fraction_order_of_iso','scheme_residueDegree_of_iso','scheme_residueDegree_of_stalk_iso'],file:'LocalPushPull.lean',paper:'proper',statement:'DVR 同构保持局部定义函数的阶数；真实 Scheme stalk 同构保持分式阶数并给出剩余域次数 1。',scope:'局部代数及实际 stalk/residue-field API 已验证。尚未证明 proper birational 与正规性自动产生余维一处的 stalk 同构。',inputs:['已给定的 DVR 局部环和环同构。','分式表示的分子与分母非零。','实际 Scheme stalk map 的 IsIso 条件。'],steps:[['阶数不变','把非零元素写成单位乘 uniformizer 的幂，同构保持这个幂次。'],['分式阶数','ord(a/b)=ord(a)−ord(b)；交叉相乘证明表示无关。'],['真实 stalk','在 Scheme.stalkMap 为同构时应用局部阶数计算。'],['次数为一','stalk 同构诱导剩余域同构，因此 residueDegree=1。']]});
nodes.push({id:'codimone',title:'正规底上余维一处同构',status:'assumption',x:20,y:1800,deps:[],paper:'proper',statement:'从 proper birational π 与正规底，构造包含所有余维一点的同构开集。',scope:'这是需要从态射与局部环性质建立的几何存在定理；不是另一个推出有效性的假设。标准参考为 Stacks 0BFP。',inputs:['正规 Noetherian 底在余维一处的局部环是 DVR。','proper birational 态射在这些点上是局部同构。','因此构造非例外严格变换和实际 stalk 同构。'],steps:[['正规局部环','余维一正规局部环为 DVR。'],['适当双有理性','利用 DVR 上的论证证明态射在该点附近为同构。'],['严格变换','取这个同构开集里的对应点，得到唯一严格变换。']]});
nodes.push({id:'localcartier',title:'Cartier 局部方程与 Weil cycle',status:'assumption',x:20,y:1920,deps:['localorder'],paper:'proper',statement:'用非零有理局部方程构造 Cartier 除子及其拉回的 underlying Weil cycle；严格变换的系数由 DVR 阶数给出。',scope:'局部阶数的表示无关与同构不变已证明。局部方程的粘合、实际 Cartier 拉回，以及有限／局部有限支撑的构造尚未完成。',inputs:['实际 Cartier 除子的局部定义函数与单位粘合数据。','沿 π 的有理函数拉回。','ord 给出 Weil 系数且满足局部有限支撑。'],steps:[['构造 Cartier 数据','把局部有理方程按单位粘合，并定义真实拉回。'],['构造 Weil cycle','在每个余维一点取局部 DVR 阶数并证明局部有限性。'],['核对严格变换','用已证明的阶数不变得到原系数。']]});
nodes.push({id:'pushpullcriterion',title:'真实 cycle 的局部推拉判据',status:'conditional',x:278,y:1680,deps:['geomcycle','localorder','codimone','localcartier'],decl:'scheme_pushpull_of_local_isomorphisms',related:['scheme_pushpull_of_local_coefficients'],file:'LocalPushPull.lean',paper:'proper',statement:'严格变换处系数一致且实际 stalk map 为同构，其余非零分量降维，则真实 cycle 推出等于 D。',scope:'直接证明 AlgebraicCycle.map π wx wy lifted=D，不再把整个 hleft 等式当参数。严格变换、stalk 同构、实际 Cartier 系数与维数选择仍需由几何构造给出。',inputs:['hcoeff：lifted(strict y)=D(y)。','hsection：D(y)非零时 π(strict y)=y。','hweight：非例外分量和像的权重相同。','hstalk：这些严格变换处的真实 stalkMap 为 IsIso。','hexceptional：其余分量的系数为零或维数／权重下降。'],steps:[['移除例外贡献','权重下降给 mapCoeff=0，因此没有推出贡献。'],['严格变换次数','由真实 stalk 同构推出 residueDegree=1。'],['恢复原系数','每个底上点只剩严格变换的一个非零贡献，等于 D(y)。'],['cycle 等式','逐点 ext 得到 π_*lifted=D。']]});
nodes.find(n=>n.id==='pushpull').deps=['pushpullcriterion'];
nodes.find(n=>n.id==='pushpull').scope='真实 cycle 的逐系数推拉推导已完成；仍待从正规 proper birational 几何构造余维一同构开集，以及实际 Cartier 局部方程／拉回的 Weil cycle。';

// Separate Theorem 1.4(2) from the effectivity argument in 1.4(1).
Object.assign(find('projective2'), {
 title:'独立结论：纤维支撑 (1.4(2))',
 statement:'设 f:X→Y 为正规簇间 projective birational 态射，D 为有效 R-Cartier 除子且 −D 为 f-nef。则每个纤维与 Supp D 不相交，或包含于其中。',
 scope:'原稿 Theorem 1.4(2) 的独立结论，不用于第 (1) 项的有效性证明。这里只通过 fiberdown 下降到 proper 版本的第 (2) 项。单有 D 有效不足以推出此结论。',
 inputs:['f 是正规簇间 projective birational 态射。','D 为有效 R-Cartier 除子，−D 为 f-nef。','需要真实连通纤维、纤维内曲线及交数的几何实现。'],
 steps:[['假定纤维遇到支撑','若该纤维不包含在支撑内，取遇到支撑但不被包含的纤维内曲线 C。'],['有效性与 nef 矛盾','D·C>0，而 −D 为 f-nef 给 D·C≤0。因此整条纤维包含在支撑内。'],['独立用途','用于 proper 版本第 (2) 项的支撑下降；第 (1) 项不依赖它。']]
});
find('proper').statement='正规簇间 proper birational f，D 为 R-Cartier 且 −D 为 f-nef：第 (1) 项是 D 有效 ⇔ f_*D 有效；第 (2) 项是在 D 有效时的纤维支撑二择一。';
find('proper').scope='两条独立的目标分支。properreduce 证明第 (1) 项的归约；fiberdown 处理第 (2) 项，不是第 (1) 项的前提。完整几何证明仍未完成。';
nodes.push(
 {id:'dvrfoundation',title:'正规一维局部环 ⇒ DVR',status:'done',x:20,y:2040,deps:[],decl:'normal_one_dimensional_local_isDVR',related:['scheme_normal_one_dimensional_stalk_isDVR'],file:'LocalGeometry.lean',paper:'proper',statement:'Noetherian、局部、整闭的整环若 Krull 维数为 1，则为 DVR；已接到真实 integral Scheme 的 stalk。',scope:'复用 mathlib 的 DVR 刻画，DVR 不再作为这条引理的输入。几何余维一与 stalk 维数 1 的对应仍需证明。',inputs:['Noetherian、局部、整闭整环。','ringKrullDim R = 1。'],steps:[['排除域','域的 Krull 维数为 0，与维数 1 矛盾。'],['唯一非零素理想','维数至多 1 使每个非零素理想都等于局部环极大理想。'],['使用已验证刻画','由整闭性与唯一非零素理想得到 PID，排除域后得到 DVR。']]},
 {id:'valuative',title:'proper 赋值判据：DVR 提升',status:'done',x:20,y:2160,deps:[],decl:'proper_dvr_lift',related:['proper_valuative_lift_unique'],file:'LocalGeometry.lean',paper:'proper',statement:'真实 proper Scheme 态射的 DVR／分式域交换方块存在唯一提升。',scope:'直接接入 mathlib 已证明的 proper 和 separated 赋值判据。双有理应用中的泛点映射和交换方块仍需构造；本节点没有假设提升存在。',inputs:['真实 Scheme 态射 f 及 IsProper f。','DVR R、其分式域 K，以及给定的交换方块。'],steps:[['proper 判据','从 IsProper f 得到 ValuativeCriterion f。'],['存在提升','对 DVR 方块提取提升及两条交换三角形。'],['唯一性','proper 蕴含 separated，其赋值判据给提升唯一。']]},
 {id:'zmtfinite',title:'mathlib：Zariski 主定理推论',status:'done',x:20,y:2280,deps:[],decl:'proper_quasiFinite_isFinite',related:['proper_finite_fiber_neighborhood'],file:'LocalGeometry.lean',paper:'support',statement:'proper + quasi-finite ⇒ finite；proper 态射的有限纤维有邻域使限制态射 finite。',scope:'这是 mathlib 已完成定理的复用，已在项目固定版本编译。不等于已证明正规底上的 finite birational 态射为同构，也不等于已证明 exceptional 点的曲线存在。',inputs:['IsProper f；第一条另需 LocallyQuasiFinite f。','第二条需 (f⁻¹{y}).Finite。'],steps:[['已有定理','复用 IsFinite.of_isProper_of_locallyQuasiFinite。'],['有限纤维邻域','复用 exists_isFinite_morphismRestrict_of_finite_preimage_singleton。'],['仍需几何桥接','结合双有理性与正规性得到同构，再连接正维纤维中的曲线存在。']]}
);
find('codimone').deps=['dvrfoundation','valuative'];
find('codimone').inputs=['正规一维 Noetherian 局部环为 DVR 已证明；仍需识别几何余维一和 stalk 维数。','proper 赋值方块存在唯一提升已接入；仍需构造双有理泛点方块并推出邻域同构。','从同构开集构造严格变换及实际 stalk 同构。'];
find('cover').deps=['zmtfinite'];
find('cover').inputs=['Zariski 主定理及 proper quasi-finite ⇒ finite 已在 mathlib；仍需 finite birational 到正规底的同构推论。','正维射影纤维中经过指定点的曲线存在性。'];

// Exact upstream sources used by the verified library integrations.
const mathlibSource='https://github.com/leanprover-community/mathlib4/blob/2a885768dae569d938bb9ff3474da6a8753bb90a/Mathlib/';
find('dvrfoundation').upstream=[['mathlib · DVR characterization',mathlibSource+'RingTheory/DiscreteValuationRing/TFAE.lean']];
find('valuative').upstream=[['mathlib · Valuative criterion',mathlibSource+'AlgebraicGeometry/ValuativeCriterion.lean']];
find('zmtfinite').upstream=[['mathlib · Zariski’s main theorem',mathlibSource+'AlgebraicGeometry/ZariskisMainTheorem.lean']];
find('geomcycle').upstream=[['mathlib · Actual algebraic cycles',mathlibSource+'AlgebraicGeometry/AlgebraicCycle/Basic.lean']];

// Proved affine geometry; keep the remaining global construction explicit.
nodes.push(
 {id:'affinesections',title:'仿射拟凝聚层的非零截面',status:'done',x:20,y:2400,deps:[],decl:'affine_quasicoherent_exists_nonzero_section',file:'AffineSections.lean',paper:'antiample',statement:'真实 Spec R 上，非零拟凝聚 O 模存在非零全局截面。',scope:'使用 mathlib 的仿射拟凝聚层—模等价证明；不是把截面存在性作为假设。仍需证明本题的 f_*O_X(−A) 拟凝聚且非零。',inputs:['M 是 Spec R 上的真实 O 模且拟凝聚。','M 非零（¬ IsZero M）。'],steps:[['反设所有截面为零','全局截面模是零对象。'],['仿射等价','拟凝聚 M 同构于其全局截面模的 tilde 层，因而也为零。'],['矛盾','与 M 非零矛盾，得到非零全局截面。']]},
 {id:'normalfinite',title:'正规底上的仿射有限双有理同构',status:'done',x:20,y:2520,deps:[],decl:'finite_birational_spec_isIso',related:['integral_birational_algebraMap_bijective','finite_birational_algebraMap_bijective'],file:'NormalBirational.lean',paper:'support',statement:'R 为整闭整环，S 为有限 R-代数且可嵌入 Frac(R) 时，Spec S→Spec R 是同构。',scope:'环映射的双射性与实际 Spec 态射的 IsIso 均已证明。一般正规双有理态射到这些仿射数据的转换及开集拼接尚未完成。',inputs:['R 是整闭整环，K 是它的分式域。','S 是有限 R-模。','j:S→ₐ[R]K 是单射；这是明确的双有理代数数据。'],steps:[['有限推出整性','S 的每个元素均在 R 上整。'],['整闭性','j(s)∈Frac(R) 在 R 上整，所以来自某个 r∈R。'],['单射性恢复元素','j 单射给 s=r，故 R→S 满射；分式域嵌入给单射。'],['实际 Spec 同构','环同构经 Spec 反变函子得到概形同构。']]}
);
find('affinesections').upstream=[['mathlib · Affine quasicoherent sheaves',mathlibSource+'AlgebraicGeometry/Modules/Tilde.lean']];
find('normalfinite').upstream=[['mathlib · Integral closure',mathlibSource+'RingTheory/IntegralClosure/IntegrallyClosed.lean']];
Object.assign(find('antiample'),{
 deps:['affinesections'],
 scope:'第一步由 projective 闭嵌入直接取 i*O(1)，是 very ample 的定义性构造。仿射非零拟凝聚层有非零截面这一通用步骤已验证。仍需接入 O(1)、直接像及其拟凝聚/非零性，并构造截面的有效 Cartier 零除子。',
 inputs:['projective 闭嵌入 i:X→P^n_R；取 L=i*O(1)≅O_X(A)。无需另证 A 的深层存在定理。','证明 F=f_*L⁻¹ 是拟凝聚且非零，应用 affinesections。','从非零截面 s 构造 E=−A+div(s)，证明有效性与 O_X(−E)≅L。'],
 steps:[['定义性选取 A','由 projective 的闭嵌入取 L=i*O(1)。它为 f-very ample，因而 f-ample；当前库仍需这些几何对象的接口。'],['证明直接像非零','F=f_*L⁻¹ 在双有理同构稠密开集上为可逆层，所以非零；还需拟凝聚性。'],['仿射非零截面：已验证','对拟凝聚且非零的 F 应用 affine_quasicoherent_exists_nonzero_section，取得 s。'],['截面到有效除子','令 E=−A+div(s)。证明这是有效 Cartier 除子，O_X(−E)≅L，从而 −E 为 f-ample；此几何桥接尚未完成。']]
});
find('cover').deps=['zmtfinite','normalfinite'];
find('cover').inputs=['proper quasi-finite ⇒ finite 已复用；正规底的有限双有理同构已完成仿射环与 Spec 版本，仍需一般概形的仿射化和拼接。','正维射影纤维中经过指定点的曲线存在性。'];

// Verified curve-local geometry and the actual pullback square.
nodes.push(...[
  {
    "id": "curvefiberdegree",
    "title": "有限平坦曲线的局部次数",
    "status": "done",
    "x": 20,
    "y": 2700,
    "decl": "finite_flat_fiber_functionField_degree",
    "file": "CurveDegree.lean",
    "statement": "实际有限平坦代数中，素点纤维满足 Σ e_q f_q=[L:K]，其中 K、L 是两端分式域。",
    "scope": "真实 ramificationIdx、inertiaDeg 与函数域；复用 mathlib 的纤维长度公式。不假设射影交数等式。",
    "inputs": [
      "R→S 为整环上的有限平坦代数；p 为素理想，素点纤维给定 Fintype。",
      "K、L 是对应分式域，带兼容的代数结构。"
    ],
    "steps": [
      [
        "纤维长度",
        "复用 Σ e_q f_q=rank_R S。"
      ],
      [
        "函数域次数",
        "分式域上的维数等于有限平坦模的秩。"
      ],
      [
        "带符号系数",
        "对任意 n∈ℤ，纤维贡献为 n·[L:K]。"
      ]
    ],
    "deps": [],
    "related": [
      "finite_flat_fiber_degree",
      "finite_flat_signed_point_degree"
    ],
    "paper": "proper"
  },
  {
    "id": "curveorder",
    "title": "局部方程的阶数拉回",
    "status": "done",
    "x": 20,
    "y": 2700,
    "decl": "heightOneOrder_pullback",
    "file": "CurveDegree.lean",
    "statement": "真实 Dedekind 环与分式域上，ord_q(h*a)=e_q·ord_p(a)，乘积的阶数可加。",
    "scope": "从 mathlib 的规范化 adic valuation 定义阶数并证明；并非把 Cartier 系数兼容性作为假设。此处是仿射正规曲线的局部方程。",
    "inputs": [
      "R、S 是 Dedekind 整环，S 为 R 上无挠代数。",
      "p、q 是实际 height-one primes，q lies over p；a 是非零有理函数。"
    ],
    "steps": [
      [
        "实际赋值",
        "ord_p(a)=−log(v_p(a))。"
      ],
      [
        "赋值拉回",
        "v_q(h*a)=v_p(a)^e_q。"
      ],
      [
        "取对数",
        "得到 ord_q(h*a)=e_q ord_p(a)。"
      ]
    ],
    "deps": [],
    "related": [
      "heightOneOrder_mul"
    ],
    "paper": "proper"
  },
  {
    "id": "localprojection",
    "title": "局部射影公式：阶数与剩余域次数",
    "status": "done",
    "x": 20,
    "y": 2700,
    "decl": "finite_flat_order_fiber_degree",
    "file": "CurveDegree.lean",
    "statement": "有限平坦仿射 Dedekind 曲线中，Σ ord_q(h*a)·f_q=ord_p(a)·[L:K]。",
    "scope": "两侧使用真实阶数、分歧指数及剩余域次数，等式已验证。仍需在完整曲线上拼接，才得到线丛的全局次数公式。",
    "inputs": [
      "有限平坦的 Dedekind 环扩张，带兼容分式域 K→L。",
      "p 为实际非零素点，a∈Kˣ；纤维中的素点可有限枚举。"
    ],
    "steps": [
      [
        "构造纤维点",
        "lying-over 的素理想非零，得到实际 height-one 点 q。"
      ],
      [
        "代入阶数公式",
        "把 ord_q(h*a) 写成 e_q ord_p(a)。"
      ],
      [
        "计算纤维贡献",
        "由 Σ e_q f_q=[L:K] 得到所需等式。"
      ]
    ],
    "deps": [
      "curveorder",
      "curvefiberdegree"
    ],
    "related": [],
    "paper": "proper"
  },
  {
    "id": "principaldivisor",
    "title": "仿射曲线的主 Weil 除子",
    "status": "done",
    "x": 20,
    "y": 2700,
    "decl": "affinePrincipalDivisor_effective_iff",
    "file": "PrincipalDivisors.lean",
    "statement": "非零有理函数给出真正有限支撑的主 Weil 除子；有效当且仅当函数属于坐标环，零除子当且仅当它是坐标环单位。",
    "scope": "真实 Dedekind 坐标环和 adic valuations。有限支撑及单位变换不变性都已证明；不是任意系数模型。完整曲线的全局 Cartier 拼接和次数仍未构造。",
    "inputs": [
      "R 是实际 Dedekind 整环，K=Frac(R)。",
      "a∈Kˣ 是非零有理函数。"
    ],
    "steps": [
      [
        "有限支撑",
        "有非零阶数的点位于 a 或 a⁻¹ 的有限极点集合中。"
      ],
      [
        "构造主除子",
        "以 ord_p(a) 为系数构造 Finsupp。"
      ],
      [
        "单位变换",
        "乘以 R 的单位不改变系数，除子可加且反演取负。"
      ],
      [
        "有效性与零判据",
        "无极点推出 a 属于 R；a 与 a⁻¹ 均正则时 a 是 R 的单位。"
      ]
    ],
    "deps": [
      "curveorder"
    ],
    "related": [
      "heightOneOrder_finite_support",
      "affinePrincipalDivisor_apply",
      "affinePrincipalDivisor_mul",
      "heightOneOrder_regular_unit",
      "affinePrincipalDivisor_unit_transition",
      "heightOneOrder_nonneg_iff",
      "affinePrincipalDivisor_inv",
      "affinePrincipalDivisor_eq_zero_iff"
    ],
    "paper": "proper"
  },
  {
    "id": "pullbackdiagram",
    "title": "曲线交换图的拉回同构",
    "status": "done",
    "x": 20,
    "y": 2700,
    "decl": "curve_square_pullback_iso",
    "file": "PullbackDiagram.lean",
    "statement": "交换图 Γ→X′、C→X 中，两条路径对真实模层的拉回同构：i*π*L≅h*j*L。",
    "scope": "直接使用真实 Scheme.Modules.pullback 的复合与相等态射同构。交换关系是图的条件；没有假设交数射影公式。全局次数公式是另一步。",
    "inputs": [
      "四个真实 Scheme 及态射 i、π、h、j，满足 i≫π=h≫j。",
      "L 为底上任意实际模层；应用时取 𝒪_X(D)。"
    ],
    "steps": [
      [
        "复合拉回",
        "i*π*L≅(π∘i)*L。"
      ],
      [
        "交换图",
        "π∘i=j∘h，所以两条复合相等。"
      ],
      [
        "分解另一条路径",
        "(j∘h)*L≅h*j*L，拼接同构。"
      ]
    ],
    "deps": [],
    "related": [],
    "paper": "proper"
  }
]);

find('projection').deps=['geomcycle','realspan','pullbackdiagram','localprojection','principaldivisor'];
find('projection').scope='交换图上真实模层的拉回同构、仿射 Dedekind 曲线的阶数拉回与局部次数公式均已验证。尚需定义完整曲线的线丛次数并拼接局部结果，接入实际 Cartier 交数，才完成整个射影公式。';
find('projection').inputs=['已验证：交换图 i*π*L≅h*j*L、ord_q(h*a)=e_q ord_p(a)、Σe_qf_q=[k(Γ):k(C)]。','待完成：对完整整曲线 h:Γ→C，构造线丛次数并证明 deg(h*L)=[k(Γ):k(C)]deg(L)，包括正规化及像为点的情形。','将这个次数公式实例化为 Cartier 交数，再应用已验证的实线性延伸。'];
find('projection').steps=[['限制到曲线：拉回同构已验证','用 Γ→X′、C→X 的交换图得到 i*π*𝒪(D)≅h*j*𝒪(D)。','curve_square_pullback_iso'],['局部阶数与次数：已验证','仿射正规曲线上，阶数按分歧指数拉回，纤维剩余域次数加权后为函数域次数倍。','finite_flat_order_fiber_degree'],['完整曲线的次数：待完成','拼接局部方程，证明线丛次数公式；接入正规化以及像为点时次数为零。'],['回到交数','令 L=j*𝒪(D)，得到 (π*D)·Γ=deg(h*L)=r deg L=D·π_*[Γ]；再使用实线性延伸。']];
find('projection').precise.zh.gap='已验证交换图的真实模层拉回同构，以及仿射 Dedekind 曲线上的局部阶数和剩余域次数计算。剩余目标是完整曲线上的 deg(h*L)=r·deg(L)，并把真实 Cartier 交数定义接到它；还需处理正规化及像为点的情形。现有 hcompat 参数尚不能删除。';
find('projection').precise.en.gap='Pullback around the actual Scheme-module square and the local order / residue-degree computation on affine Dedekind curves are proved. The remaining goal is deg(h*L)=r·deg(L) on complete curves, connected to actual Cartier intersection, including normalization and the point-image case. The existing hcompat parameter cannot yet be removed.';
find('curvefiberdegree').upstream=[['mathlib · Finite flat fiber degree',mathlibSource+'RingTheory/RamificationInertia/Basic.lean']];
find('curveorder').upstream=[['mathlib · Valuations under extension',mathlibSource+'NumberTheory/RamificationInertia/Valuation.lean']];
find('principaldivisor').upstream=[['mathlib · Finite valuation support',mathlibSource+'RingTheory/DedekindDomain/FiniteAdeleRing.lean']];
find('pullbackdiagram').upstream=[['mathlib · Actual module-sheaf pullbacks',mathlibSource+'AlgebraicGeometry/Modules/Sheaf.lean']];

// User-guided point-divisor, closed-point and ring-theoretic routes.
nodes.push(...[
  {
    "id": "pointtensor",
    "title": "点除子的张量拉回与重数",
    "status": "done",
    "x": 278,
    "y": 2780,
    "deps": [
      "curvefiberdegree"
    ],
    "decl": "finite_flat_point_pullback_degree_over_base",
    "related": [
      "point_pullback_tensor_iso",
      "point_pullback_tensor_length",
      "finite_flat_point_pullback_degree"
    ],
    "file": "PointPullback.lean",
    "paper": "proper",
    "statement": "点 p 的实际张量拉回在 q 处有有限长度 m_q；Σm_q[k(q):k]=[L:K][k(p):k]。",
    "scope": "用户提出的点除子计数路线已完成仿射局部代数版本。商环同构、长度有限性、重数等于分歧指数及基域次数权重均已证明。仍需将一般线丛表示为除子、在完整曲线上拼接并接入正规化。",
    "inputs": [
      "R、S 是域 k 上有限型 Dedekind 坐标环，S 是有限平坦 R-代数。",
      "p 是实际非零素点；q 是 lying-over 的素点。",
      "K、L 为兼容分式域；素点纤维可有限枚举。"
    ],
    "steps": [
      [
        "点的张量拉回",
        "S_q/𝔪_pS_q ≅ S_q⊗_R(R/𝔪_p)，直接复用实际商环—张量同构。"
      ],
      [
        "计算重数",
        "quasi-finite 与 Noetherian 性保证长度有限；m_q=length(S_q⊗_R R/𝔪_p)=e_q。"
      ],
      [
        "数原像并计重",
        "Σm_q[k(q):k(p)]=[L:K]。"
      ],
      [
        "计入点的基域次数",
        "剩余域次数的塔公式给 Σm_q[k(q):k]=[L:K][k(p):k]。"
      ]
    ]
  },
  {
    "id": "closedpoint",
    "title": "归零分量的支撑外闭点",
    "status": "done",
    "x": 20,
    "y": 2900,
    "deps": [],
    "decl": "finiteType_exists_closedPoint_outside_support",
    "related": [
      "exists_closedPoint_outside_support"
    ],
    "file": "CurveSelection.lean",
    "paper": "projective",
    "statement": "域上有限型实际概形中，若闭集 F 不被闭支撑 Z 包含，则存在闭点 x∈F∖Z。",
    "scope": "已从 mathlib 的 Jacobson 性导出闭点存在，不把“存在 x”另作假设。应用时 F⊄Supp(D+eE) 来自归零系数及真实 Weil 支撑解释；经过 x 的压缩曲线仍需几何构造。",
    "inputs": [
      "实际概形 X 局部有限型于域 k。",
      "F、Z 为闭集，且 F⊄Z。"
    ],
    "steps": [
      [
        "非空差集",
        "F⊄Z 给 F∖Z 非空。"
      ],
      [
        "局部闭性",
        "F 闭且 Z 闭，所以 F∖Z 为局部闭集。"
      ],
      [
        "Jacobson 性",
        "域上有限型概形为 Jacobson，非空局部闭集包含闭点。"
      ]
    ]
  },
  {
    "id": "localidempotents",
    "title": "局部环的幂等元与非平凡分解",
    "status": "done",
    "x": 20,
    "y": 3020,
    "deps": [],
    "decl": "localRing_idempotent_trivial",
    "related": [
      "localRing_not_product_nontrivial"
    ],
    "file": "LocalConnectedness.lean",
    "paper": "fiber",
    "statement": "真实局部环中，a²=a 蕴含 a=0 或 a=1；局部环不能分解成两个非零环的直积。",
    "scope": "已完成 Hartshorne III §11／形式函数连通性论证的最后一个环论矛盾。尚未形式化把断开的几何纤维提升为完备局部环中的非平凡幂等元，所以未宣称连通纤维定理已完成。",
    "inputs": [
      "R 是实际交换局部环。",
      "a²=a；或给定 R≅A×B，且 A、B 非零。"
    ],
    "steps": [
      [
        "局部环单位二择一",
        "a 与 1−a 至少一个是单位。"
      ],
      [
        "消去单位",
        "a²=a 分别给 a=1 或 a=0。"
      ],
      [
        "排除非零直积",
        "直积中的 (1,0) 是非平凡幂等元，与前一步矛盾。"
      ]
    ]
  }
]);

find('projection').deps.push('pointtensor');
find('projection').steps[1]=['点除子的张量计数：已验证','S_q⊗_R(R/𝔪_p) 的长度给真实重数，按剩余域次数加权后为函数域次数倍。','finite_flat_point_pullback_degree_over_base'];
find('projection').precise.zh.gap='交换图拉回、点除子的张量拉回商环、有限长度重数和次数加权计数均已验证。接下来按点除子的可加性延伸，并构造完整曲线的线丛次数及正规化兼容性，将真实 Cartier 交数接到 deg(h*L)=r·deg(L)。hcompat 尚未从完整几何证明。';
find('projection').precise.en.gap='The pullback square, tensor quotient for a point divisor, finite local multiplicities and residue-degree-weighted counting are verified. Extend by additivity of point divisors, construct complete-curve line-bundle degree and normalization compatibility, then connect actual Cartier intersection to deg(h*L)=r·deg(L). Full geometric hcompat remains open.';
find('curves').deps=['max','negative','support','closedpoint','cover'];
find('curves').statement='e 的构造给负 exceptional 分量 F 在 D+eE 中系数为零。取闭点 x∈F∖Supp(D+eE)，再在 F 内取经过 x 的压缩曲线。';
find('curves').scope='最大比值与归零系数已验证；域上有限型概形的支撑外闭点存在也已验证。零系数说明 F 不是支撑分支，并不说明 F 与支撑完全不相交。剩余是实际 Weil 支撑解释及 F 内压缩曲线的几何构造；不依赖第二部分的连通纤维。';
find('curves').inputs=['反设 D 不有效且 f_*D 有效，负分量为 exceptional。','E 有效并包含 exceptional locus，故这些分量的 E 系数为正。','最大比值步骤得到 coeff_F(D+eE)=0；实际支撑解释给 F⊄Supp(D+eE)。','支撑外闭点已可选；还需从 f|F 的正维纤维中构造经过 x 的完整曲线。'];
find('curves').steps=[['由 e 取得归零分量','e=max(−coeff_P(D)/coeff_P(E))，得到 D+eE 有效及某个负分量 F 的系数为零。','exists_effective_shift'],['选择支撑外闭点：已验证','F 不是支撑分支，所以 F⊄Supp(D+eE)。有限型概形的闭点引理给 x。','finiteType_exists_closedPoint_outside_support'],['在 F 内取曲线：待补几何','F 为 exceptional divisor，f|F 有正维纤维。在包含 x 的纤维内取完整曲线 C⊂F；由于 x 在支撑外，C 不被支撑包含。']];
find('connected').deps=['normalfinite','localidempotents','cover'];
find('connected').title='连通纤维与相交曲线（第二部分）';
find('connected').statement='第二部分的几何支撑二择一路线：连通纤维若部分遇到支撑，需构造遇支撑却不被包含的纤维内曲线；高维选择步骤待修补。';
find('connected').scope='仅用于纤维支撑二择一，第 (1) 部分及 proper 有效性下降不使用此节点。连通性按 Hartshorne III §11 的正规性、形式函数与幂等元路线推进；最后局部环矛盾已验证。一般高维纤维的相交曲线选择尚未完成，不能仅从 exceptional 曲线覆盖直接断言所需相交条件。';
find('connected').inputs=['先证明 f_*𝒪_X=𝒪_Y：双有理性给分式域嵌入，proper 直接像有限性与整闭性恢复基环。','形式函数：Â≅lim H⁰(X_n,𝒪_Xn)。断开纤维给各阶兼容的非平凡幂等元；这一几何桥接尚待形式化。','局部环不存在非平凡幂等元已验证，得到矛盾后可推出连通纤维。','压缩曲线覆盖复用 cover；还需修补曲线同时遇支撑且不被包含的选择，不将覆盖误当成这个更强结论。'];
find('connected').steps=[['正规性恢复结构层','利用 proper 的直接像有限性及双有理分式域嵌入，整闭性给 f_*𝒪_X=𝒪_Y；环论核心在 normalfinite。'],['形式函数与幂等元：待补几何','若纤维断开，各无穷小邻域产生兼容非平凡幂等元。形式函数把它送入基上完备局部环。'],['局部环矛盾：已验证','局部环幂等元只有 0、1，排除非平凡分解。','localRing_idempotent_trivial'],['高维相交曲线：待修补','复用曲线覆盖基础，但还需保证曲线遇支撑且不包含于支撑。此步只属于第二部分。']];
find('pointtensor').upstream=[['mathlib · Ideal quotient and tensor base change',mathlibSource+'RingTheory/TensorProduct/Quotient.lean'],['mathlib · Multiplicity as local length',mathlibSource+'RingTheory/RamificationInertia/Ramification.lean']];
find('closedpoint').upstream=[['mathlib · Jacobson closed-point selection',mathlibSource+'Topology/JacobsonSpace.lean']];
find('connected').upstream=[['Stacks · Formal functions and idempotent argument','https://stacks.math.columbia.edu/tag/03H0'],['Stacks · Normal proper connectedness','https://stacks.math.columbia.edu/tag/0AY8']];

// Prime-divisor pushforward: the exact geometric facts used by part (1).
Object.assign(find('strict'),{
 title:'素除子严格变换与推出系数',
 deps:['codimone','geomcycle','localorder'],
 statement:'D=Σa_P[P] 是素除子的有限形式和。对底上素除子 Q，唯一严格变换 Q̃ 推出为 Q；exceptional 素除子推出为零，故 coeff_Q(f_*D)=coeff_Q̃(D)。',
 scope:'cycle 在这里就是除子的形式和。需要构造真实严格变换、证明余维一同构给函数域次数 1，并选择实际维数权重。已验证的 Scheme-cycle 推出公式与 stalk 同构次数为 1 可复用；余维一同构开集的几何构造仍待完成。',
 inputs:['明确性质：proper birational f:X→Y 且 Y 正规时，对每个素除子 Q 的泛点 η_Q，存在其开邻域 U，使 f⁻¹(U)→U 为同构。','唯一严格变换 Q̃ 的函数域等于 k(Q)，所以 f_*[Q̃]=[Q]。','若 codim_Y f(P)≥2，则素除子 P 在除子推出中贡献为零。','由 D=Σa_P[P] 的有限和可加性，推出 coeff_Q(f_*D)=coeff_Q̃(D)。'],
 steps:[['明确对象','D 是素除子的有限实系数形式和。这里的 cycle 保留实际除子系数。'],['构造严格变换','在 Q 泛点的同构邻域上取对应素点，再取闭包得到 Q̃。几何同构开集仍待证明。'],['计算推出','同构给函数域次数 1；被压缩的除子降维贡献 0。已有实际 AlgebraicCycle.map 公式。'],['得到负分量结论','若 f_*D 有效，所有非 exceptional 分量系数均非负；因此负分量必为 exceptional。']]
});
find('curves').deps.push('strict');

// Release 11: actual codimension-one geometry and user-guided routes.
nodes.push(...[
  {
    "id": "modsurj",
    "title": "proper 双有理态射的满射性",
    "status": "done",
    "statement": "proper 双有理态射到整概形为满射。",
    "scope": "实际 Scheme 态射：非空同构开集稠密，proper 的闭映射性质使像等于整个底。无需额外假设满射。",
    "inputs": [
      "Y 整，f proper 且在非空开集为同构。"
    ],
    "steps": [
      [
        "稠密像",
        "同构开集包含于像，且在整底上稠密。"
      ],
      [
        "闭像",
        "proper 给闭映射，稠密闭像即整个底。",
        "proper_birational_surjective"
      ]
    ],
    "deps": [],
    "decl": "proper_birational_surjective",
    "file": "CodimensionOne.lean",
    "x": 278,
    "y": 2900,
    "paper": "proper"
  },
  {
    "id": "hartshornegraph",
    "title": "Hartshorne：实际图像闭包",
    "status": "conditional",
    "statement": "非空开集 U→P 的图像闭包 Z⊂X×_S P 给 proper 双有理满射 Z→X 及 proper Z→P。",
    "scope": "真实 scheme-theoretic image 的构造已验证。P→S proper 及 U 上的映射是本构造的输入；有限覆盖产生这些映射并使整体射影，仍属于完整 Chow 引理。",
    "inputs": [
      "X 整且 Noetherian 拓扑，X→S 与 P→S proper。",
      "非空开集 U⊂X 上给实际态射 g:U→P，满足到底 S 的交换关系。"
    ],
    "steps": [
      [
        "取实际图像",
        "构造 graph:U→X×_S P，再取 graph.image。"
      ],
      [
        "证明双有理",
        "graph.toImage 为稠密开嵌入，分离投影的稠密开截面给 U 上同构。",
        "isIso_over_dense_open_section"
      ],
      [
        "proper 与满射",
        "闭嵌入和 proper 投影复合给 proper；双有理到整底的闭稠密像给满射。",
        "hartshorne_graph_closure"
      ]
    ],
    "deps": [
      "modsurj"
    ],
    "decl": "hartshorne_graph_closure",
    "file": "HartshorneGraph.lean",
    "related": [
      "isIso_over_dense_open_section"
    ],
    "x": 278,
    "y": 2900,
    "paper": "proper"
  },
  {
    "id": "relativesigns",
    "title": "相对 nef 与曲线正性的取负符号",
    "status": "done",
    "statement": "在被 f 压缩的曲线上，nef(−D) ⇔ D·C≤0；curvePositive(−E) ⇔ E·C<0。",
    "scope": "验证相对数值定义和线性取负。curvePositive 仅指所有压缩曲线上的严格正次数，不声称等价于几何 f-ample。",
    "inputs": [
      "给定压缩曲线谓词及线性交数。",
      "应用到几何 f-ample 时，还须用其限制到完整纤维曲线的正次数性质。"
    ],
    "steps": [
      [
        "限制测试范围",
        "只对 contracted c 的曲线量化。"
      ],
      [
        "线性取负",
        "degree(−D)=−degree(D)，将非负／严格正改写为非正／严格负。",
        "relative_nef_neg_iff"
      ]
    ],
    "deps": [],
    "decl": "relative_nef_neg_iff",
    "file": "RelativeNumerics.lean",
    "related": [
      "relative_curvePositive_neg_iff"
    ],
    "x": 278,
    "y": 2900,
    "paper": "proper"
  },
  {
    "id": "ratproduct",
    "title": "k(t) 的主除子次数零",
    "status": "done",
    "statement": "不可约因子按重数与多项式次数加权；有限零极点贡献加无穷远阶数等于 0。",
    "scope": "使用实际 RatFunc、normalizedFactors 和 inftyValuation。已证明范数路线的基域 k(t) 计算；一般曲线的范数赋值传递、闭点识别与线丛次数尚未完成。",
    "inputs": [
      "k 为任意域，a∈k(t) 非零。",
      "有限处贡献写成分子与分母不可约因子的次数和，保留实际重数。"
    ],
    "steps": [
      [
        "计算有限处",
        "不可约分解的次数和等于多项式次数。",
        "polynomial_factor_degree_sum"
      ],
      [
        "计算无穷远",
        "真实无穷远赋值给 ord∞(a)=−intDegree(a)。",
        "rationalInfinityOrder_eq"
      ],
      [
        "相加得到零",
        "分子次数减分母次数，与无穷远阶数相消。",
        "rationalFunction_principal_degree_zero"
      ]
    ],
    "deps": [],
    "decl": "rationalFunction_principal_degree_zero",
    "file": "RationalProductFormula.lean",
    "related": [
      "polynomial_factor_degree_sum",
      "rationalInfinityOrder_eq"
    ],
    "x": 278,
    "y": 2900,
    "paper": "proper"
  },
  {
    "id": "normalsections",
    "title": "正规 stalk ⇒ 正规仿射坐标环",
    "status": "done",
    "statement": "整概形的所有实际局部环整闭，则每个非空仿射开集的坐标环整闭。",
    "scope": "用实际仿射开集与其素谱对应，把 Scheme stalk 识别为坐标环的素理想局部化，再应用整闭性的局部判据。没有假设坐标环整闭。",
    "inputs": [
      "Y 整，所有实际 stalk 均整闭。",
      "非空仿射开集 U。"
    ],
    "steps": [
      [
        "识别实际局部化",
        "对每个极大理想使用 hU.fromSpec，取得对应点及其实际 stalk。"
      ],
      [
        "整闭性局部判据",
        "所有极大局部化整闭，推出 Γ(Y,U) 整闭。",
        "normal_affine_sections"
      ]
    ],
    "deps": [],
    "decl": "normal_affine_sections",
    "file": "NormalSections.lean",
    "x": 278,
    "y": 2900,
    "paper": "proper"
  }
]);
Object.assign(find("codimone"),{
  "title": "正规底上余维一处同构",
  "status": "done",
  "statement": "proper birational f:X→Y 在一个包含 Y 所有余维一点的开集 U 上为同构；对应点唯一，真实 stalk map 为同构，且仍为余维一点。",
  "scope": "完整几何存在证明已通过 Lean。使用实际 integral Scheme、coheight、stalk、proper 赋值判据及截面的 spreading out；没有假设同构邻域或 stalk 同构存在。",
  "inputs": [
    "X、Y 是整概形，Y 局部 Noetherian；f proper。",
    "给定态射 f 在非空开集上为同构，这是此处双有理态射的定义。",
    "Y 的实际局部环均整闭，表达正规性；没有假设结论中的 U。"
  ],
  "steps": [
    [
      "余维一给 DVR",
      "使用 ringKrullDim_stalk_eq_coheight，从实际 coheight=1 和正规性得到 DVR。",
      "normal_codimensionOne_stalk_isDVR"
    ],
    [
      "构造泛点方块并提升",
      "从非空同构开集取泛点逆映射，构造实际 DVR 方块，再应用 proper 赋值判据。",
      "proper_birational_isIso_near_DVR"
    ],
    [
      "铺开截面，证明为逆",
      "把局部环上的提升铺开为开邻域截面；separated 使其闭，泛点使其稠密，整概形上遂为同构。",
      "separated_dominant_section_isIso"
    ],
    [
      "合并所有邻域",
      "取各余维一点的邻域之并，利用同构的 Zariski 局部性得到统一开集。",
      "proper_birational_isIso_on_codimensionOne_open"
    ],
    [
      "对应素点及局部环",
      "证明原态射的 stalk map 同构、余维保持与纤维对应点唯一。",
      "proper_birational_codimensionOne_unique_preimage"
    ]
  ],
  "decl": "proper_birational_isIso_on_codimensionOne_open",
  "file": "CodimensionOne.lean",
  "related": [
    "generic_stalk_dominant",
    "normal_codimensionOne_stalk_isDVR",
    "separated_dominant_section_isIso",
    "proper_birational_isIso_near_DVR",
    "proper_birational_isIso_near_codimensionOne",
    "proper_birational_isIso_on_codimensionOne_open",
    "stalkMap_isIso_over_isomorphism_open",
    "proper_birational_codimensionOne_unique_preimage"
  ],
  "deps": [
    "dvrfoundation",
    "valuative"
  ]
});
Object.assign(find("cover"),{
  "title": "exceptional 闭点的曲线覆盖",
  "status": "assumption",
  "statement": "对正规底上的 projective birational f，exceptional locus 的每个闭点 x 位于一条被 f 压缩的完整曲线上。",
  "scope": "按 Zariski 主定理推进：center 是最大同构开集的补集；其上任一原像点均非 quasi-finite，需取得经过该点的正维纤维分量，再用射影截面取曲线。不能只证明整个纤维某处维数 ≥1。余维一同构已完成，但一般 center 点的判据和曲线构造仍待接入。",
  "inputs": [
    "f 为射影双有理态射，底正规；x 为 exceptional 闭点，y=f(x)。",
    "Zariski 主定理的准确推论：若在 y 的任一原像点 quasi-finite，正规性及 proper 性给 y 的同构开邻域。",
    "故 center 上纤维在每个原像点的局部维数为正；还需在包含 x 的射影分量内切出经过 x 的曲线。"
  ],
  "steps": [
    [
      "明确 center",
      "令 U 为最大同构开集，center=Y∖U。这里 f 的有理逆未定义，与实际纤维 f⁻¹(y) 不同。"
    ],
    [
      "Zariski 主定理：待接几何",
      "quasi-finite 给局部有限代数；双有理把它嵌入分式域，整闭性使其等于基环。铺开的截面由 proper/separated 成为同构。"
    ],
    [
      "局部正维：待接几何",
      "反证：若 x 处纤维局部维数为零，则 f 在 x 处 quasi-finite，使 y 属于 U，矛盾。"
    ],
    [
      "经过指定闭点的曲线：待构造",
      "在包含 x 的正维射影纤维分量内，逐次用经过 x 的超平面截到维数 1。所得完整曲线被 f 压缩。"
    ]
  ],
  "deps": [
    "zmtfinite",
    "normalfinite",
    "normalsections"
  ]
});
Object.assign(find("intersection"),{
  "title": "真实交数与正性接口",
  "status": "assumption",
  "statement": "对被 f 压缩的完整曲线 C：−D 为 f-nef 给 D·C≤0；−E 为 f-ample 给 E·C<0。还需从真实 Cartier 次数接通有效性及支撑的正性。",
  "scope": "相对 nef 的符号条件就是定义，已单独形式化其取负推论。相对 ample 的限制在完整纤维曲线上为 ample，给严格正次数；不把“曲线上严格正”误定义成几何 ample 的等价条件。剩余接口是实际交数、线性及有效除子的次数正性。",
  "inputs": [
    "C 必须是被 f 压缩的完整曲线；−D 为 f-nef、−E 为 f-ample。",
    "从 𝒪(D)|C 的真实次数构造交数及线性；f-ample 的曲线限制须接到这个次数。",
    "有效 B 且 C 不被 Supp B 包含，则 B·C≥0；若还相交，则 B·C>0。"
  ],
  "steps": [
    [
      "相对测试曲线",
      "f-nef 只测试 f 压缩的曲线；取负的数值符号等价已验证。",
      "relative_nef_neg_iff"
    ],
    [
      "相对 ample 的限制",
      "在压缩曲线上限制相对 ample 线丛，再由 ample 的正次数得到 E·C<0；数值取负推论已验证。",
      "relative_curvePositive_neg_iff"
    ],
    [
      "真实有效除子的正性：待接几何",
      "次数来自曲线上的有效除子重数；有限非负重数给非负，相交给至少一个正重数。"
    ]
  ],
  "deps": [
    "relativesigns"
  ]
});
Object.assign(find("chow"),{
  "title": "Chow 改造与几何推拉性质",
  "status": "assumption",
  "statement": "按 Hartshorne 构造射影改造，再正规化；图像闭包的 proper、双有理与满射步骤已验证，完整射影性和几何推拉尚未完成。",
  "scope": "没有把改造存在性换成显式假设后标成完成。hartshorne_graph_closure 构造真实 scheme-theoretic image 与投影；仍需有限仿射覆盖的射影嵌入组合、射影性证明及有限正规化。全局交数公式和 Cartier 推拉也仍为独立剩余任务。",
  "inputs": [
    "已完成：非空开集到 proper 辅助空间的图像闭包；改造 proper、双有理且满射。",
    "待完成：按 Hartshorne 用有限仿射覆盖与射影嵌入，证明所得改造对底射影，再正规化。",
    "待完成：真实 Cartier 射影公式、推出拉回恒等式、有效性与支撑拉回。"
  ],
  "steps": [
    [
      "图像闭包：已验证",
      "在 X×_S P 中取 scheme-theoretic image，得到实际 Z、π、q 和稠密开嵌入；proper 与双有理均已证明。",
      "hartshorne_graph_closure"
    ],
    [
      "有限覆盖与射影性：待完成",
      "按 Hartshorne 组合各仿射开集的射影嵌入，证明投影满足所需射影性。proper 投影本身不能替代这一步。"
    ],
    [
      "正规化与几何公式：待完成",
      "接入有限正规化、真实 Cartier 拉回、次数及支撑，再调用已验证的下降逻辑。"
    ]
  ],
  "deps": [
    "hartshornegraph",
    "modsurj"
  ]
});
find('codimone').related=find('codimone').related.filter(d=>d!==find('codimone').decl);
find('dvrfoundation').scope='正规一维局部环的 DVR 刻画已接入实际 stalk；codimone 现已使用 coheight 与 ringKrullDim 的对应，从几何余维一直接取得 DVR。';
find('valuative').scope='proper 与 separated 的实际赋值判据已验证；codimone 现已构造双有理泛点方块、铺开提升并证明邻域同构。';
find('localorder').scope='DVR 阶数与剩余域次数计算已验证；codimone 现已从实际 proper birational 几何提供余维一对应点的 stalk 同构。真实 Cartier 拉回系数的识别仍需接入。';
find('strict').scope='实际余维一同构开集、唯一对应素点和 stalk 同构已完成。剩余为取对应点闭包作为实际严格变换、连接真实维数权重与 Cartier 除子系数；实际 Scheme-cycle 推出公式已可复用。';
find('strict').steps[1][1]='已从 proper birational 几何构造同构开集、唯一余维一对应点及其 stalk 同构。将该点闭包接为实际素除子仍待完成。';
find('projection').deps.push('ratproduct');
find('projection').steps[2][1]='范数与赋值路线：先用已验证的 k(t) 主除子次数零，再证明一般函数域扩张中 ord_p(Na)=Σ_q f_q ord_q(a)，识别完整曲线所有闭点；得到主除子次数零后才能定义截面无关的线丛次数。';
find('projection').precise.zh.gap='已完成真实模层交换图、局部重数计数及 k(t) 主除子次数零。按函数域范数与赋值继续证明全局主除子次数零，再构造线丛次数、正规化兼容性及完整 Cartier 交数公式；hcompat 尚未删除。';
find('projection').precise.en.gap='The actual pullback square, local multiplicity counting and the k(t) principal-degree-zero calculation are verified. Continue with norm/valuation transport for general function fields, define section-independent line-bundle degree, then connect normalization and actual Cartier intersection. hcompat remains open.';
find('cover').upstream=[['Stacks · Normal-base quasi-finite-point isomorphism','https://stacks.math.columbia.edu/tag/0BFP']];

find('pushpull').scope='真实 cycle 的逐系数推拉推导已完成；余维一同构开集与实际 stalk 同构现已从正规 proper birational 几何证明。剩余为实际 Cartier 局部方程及拉回的 Weil cycle、素点闭包与维数权重。';

// Release 12: actual Cartier construction and geometric push-pull.
nodes.push(...[
  {
    "id": "rationalorder",
    "title": "有理方程的 DVR 阶数",
    "status": "done",
    "statement": "实际分式域非零元素的阶数与分式表示无关；乘法给阶数相加，实际局部单位过渡不改变阶数。",
    "scope": "用 IsFractionRing、实际 numerator/denominator 与 DVR addVal 构造，不是任意线性配对。",
    "inputs": [
      "实际 DVR R 及其分式域 K；a 是 K 中非零有理方程。"
    ],
    "steps": [
      [
        "表示无关",
        "任意非零分子分母给同一阶数。",
        "dvr_rationalOrder_represents"
      ],
      [
        "单位粘合",
        "实际局部单位阶数为零，乘法加性给方程过渡不变。",
        "dvr_rationalOrder_unit_transition"
      ]
    ],
    "decl": "dvr_rationalOrder_unit_transition",
    "file": "FractionFieldOrders.lean",
    "deps": [
      "localorder"
    ],
    "related": [
      "dvr_rationalOrder_represents",
      "dvr_rationalOrder_unit",
      "dvr_rationalOrder_mul"
    ],
    "paper": "proper",
    "x": 278,
    "y": 3100
  },
  {
    "id": "divisorsupport",
    "title": "任意维 Cartier 支撑有限性",
    "status": "done",
    "statement": "Noetherian domain 的非零元素只落在有限个高度一素理想内；实际仿射 Scheme 上的余维一非单位 germ 点也有限。",
    "scope": "用主理想的极小素理想有限性证明，不限制坐标环为 Dedekind，也不输入任何支撑有限假设。",
    "inputs": [
      "非零 section；整、局部 Noetherian Scheme 的非空仿射开集。"
    ],
    "steps": [
      [
        "主理想的极小素理想",
        "包含 r 的高度一素理想都是 (r) 上的极小素理想。",
        "finite_heightOne_primes_containing"
      ],
      [
        "接入实际仿射点",
        "用 Spec 与图册的同构，将高度和非单位 germ 识别为 coheight 与素理想条件。",
        "finite_codimensionOne_nonunit_germs"
      ]
    ],
    "decl": "finite_codimensionOne_nonunit_germs",
    "file": "CodimensionSupport.lean",
    "deps": [],
    "related": [
      "finite_heightOne_primes_containing"
    ],
    "paper": "proper",
    "x": 278,
    "y": 3100
  },
  {
    "id": "cartierpullback",
    "title": "实际 Cartier 方程拉回",
    "status": "done",
    "statement": "从 dominant Scheme 态射构造实际函数域拉回和 Cartier 拉回图册，证明泛点／局部环方块与单位过渡，并保持同构 stalk 上的阶数。",
    "scope": "拉回图册的仿射覆盖及方程在证明中构造，兼容性来自实际 stalkSpecializes_stalkMap；不假设 pullback cycle 或兼容等式。",
    "inputs": [
      "整概形间实际 dominant 态射；Cartier 方程图册。",
      "比较余维一阶数时使用正规、局部 Noetherian 及真实 stalk 同构。"
    ],
    "steps": [
      [
        "构造函数域拉回",
        "dominant 态射映泛点到泛点，给实际函数域映射。",
        "dominant_genericPoint_eq"
      ],
      [
        "证明实际交换方块",
        "泛点拉回与实际局部环映射相容。",
        "dominantFunctionFieldMap_stalk"
      ],
      [
        "构造拉回图册",
        "在逆像中选择仿射邻域，拉回方程并证明其单位过渡。",
        "exists_cartierAtlas_pullback"
      ],
      [
        "同构处保持系数",
        "拉回方程的实际分式表示与局部环同构相容，给相同 DVR 阶数。",
        "dominantFunctionFieldMap_order_of_stalk_iso"
      ]
    ],
    "decl": "exists_cartierAtlas_pullback",
    "file": "CartierPullback.lean",
    "deps": [
      "localcartier",
      "localorder"
    ],
    "related": [
      "dominant_genericPoint_eq",
      "dominantFunctionFieldMap_stalk",
      "dominantFunctionFieldMap_order_of_stalk_iso"
    ],
    "paper": "proper",
    "x": 278,
    "y": 3100
  }
]);
Object.assign(find("localcartier"),{
  "title": "Cartier 局部方程与 Weil 除子",
  "status": "done",
  "statement": "从实际整正规、局部 Noetherian Scheme 的 Cartier 方程图册，构造 mathlib Weil divisor；按单位粘合，局部有限支撑，并与方程及开覆盖选择无关。",
  "scope": "几何构造已完成。图册输入就是 Cartier 的局部方程定义：非零有理方程及局部环单位过渡。没有假设系数相等、支撑有限或已有 Weil cycle。拟紧时全局支撑有限；实际拉回另见相邻已验证节点。",
  "inputs": [
    "X 是整概形且局部 Noetherian，实际局部环整闭。",
    "Cartier 数据：仿射开覆盖、非零有理方程及实际 stalk 中的单位过渡。"
  ],
  "steps": [
    [
      "单位过渡粘合",
      "实际单位的阶数为零，各图册上的余维一阶数相同。",
      "cartierAtlas_order_agrees"
    ],
    [
      "局部支撑有限",
      "任意维仿射坐标环中，把支撑包含于分子或分母的有限个高度一素理想。",
      "finite_schemeRationalOrder_on_affine"
    ],
    [
      "构造 Weil 除子",
      "把局部系数粘合成实际 AlgebraicCycle；证明其支撑只在余维一。",
      "cartierAtlas_weilCycle_isWeilDivisor"
    ],
    [
      "覆盖与方程选择无关",
      "不同覆盖上的等价单位方程给同一个实际 Weil 除子。",
      "cartierAtlas_weilCycle_eq_of_unit_transitions"
    ]
  ],
  "decl": "cartierAtlas_weilCycle_isWeilDivisor",
  "file": "CartierAtlas.lean",
  "deps": [
    "rationalorder",
    "divisorsupport",
    "dvrfoundation"
  ],
  "related": [
    "cartierAtlas_order_agrees",
    "schemeRationalOrder_zero_of_unit_germs",
    "finite_schemeRationalOrder_on_affine",
    "cartierAtlas_coefficient_eq",
    "cartierAtlas_locallyFiniteSupport",
    "cartierAtlas_weilCycle_eq_of_unit_transitions",
    "cartierAtlas_weilCycle_finite_support"
  ],
  "paper": "proper",
  "x": 278,
  "y": 3100
});
Object.assign(find("strict"),{
  "title": "实际严格变换与推出系数",
  "status": "done",
  "statement": "构造 actual codimension-one generic points 上的 strict 单射；真实 cycle 推出系数等于严格变换系数，ExceptionalIndex 等价于像不再为余维一。",
  "scope": "已接通原来的有限支撑系数模型：weilCycleCoefficients_pushforward 证明 birationalPush 与实际 AlgebraicCycle.map 一致。素除子由其泛点表示，这是 mathlib cycle 的定义；没有另假设 strict 单射或次数一。",
  "inputs": [
    "X、Y 整概形，Y 局部 Noetherian 且实际 stalk 整闭。",
    "给定 proper birational 态射 f；转为有限系数时 X、Y 拟紧。"
  ],
  "steps": [
    [
      "构造严格变换",
      "由余维一同构定理选择唯一对应的实际素点。",
      "geometricStrictTransform_image"
    ],
    [
      "识别 exceptional",
      "证明 strict 为单射，且其像恰为映到余维一的源素点。",
      "geometric_exceptional_iff"
    ],
    [
      "计算真实推出系数",
      "唯一原像的剩余域次数为一，得到 coeff_Q(f_*D)=coeff_Q̃(D)。",
      "scheme_cycle_strictTransform_coefficient"
    ],
    [
      "接回原模型",
      "用真实 cycle 的有限支撑构造 Finsupp，证明与 birationalPush 相等。",
      "weilCycleCoefficients_pushforward"
    ]
  ],
  "decl": "weilCycleCoefficients_pushforward",
  "file": "StrictTransform.lean",
  "deps": [
    "codimone",
    "geomcycle",
    "localorder"
  ],
  "related": [
    "geometricStrictTransform_image",
    "geometricStrictTransform_injective",
    "geometric_exceptional_iff",
    "scheme_cycle_strictTransform_coefficient"
  ],
  "paper": "proper",
  "x": 278,
  "y": 3100
});
Object.assign(find("pushpull"),{
  "title": "真实 R-Cartier 除子的推拉恒等式",
  "status": "done",
  "statement": "正规整概形间 proper birational f 的实际 Cartier 拉回满足 f_*(f*D)=D，包括有限实线性组合的 R-Cartier 版本。",
  "scope": "从函数域拉回构造每个 Cartier 图册，建立真实 Weil cycle；余维一系数相等与次数一来自实际 stalk 同构。使用实际 coheight 权重和 AlgebraicCycle.map。没有 hleft、hcoeff、任意 lifted 或 exceptional 权重假设。",
  "inputs": [
    "X、Y 整、正规、局部 Noetherian；f proper birational。",
    "D 由有限个实际 Cartier 图册及实系数表示；拉回图册在证明中构造。"
  ],
  "steps": [
    [
      "构造实际拉回",
      "取逆像中的仿射邻域，拉回有理方程，并由 stalk 方块证明单位过渡。",
      "exists_cartierAtlas_pullback"
    ],
    [
      "余维一系数相等",
      "同构局部环保持实际拉回方程的 DVR 阶数。",
      "dominantFunctionFieldMap_order_of_stalk_iso"
    ],
    [
      "真实 cycle 推拉",
      "底上素点有唯一原像且次数一；其它 coheight 权重贡献为零。",
      "proper_birational_weil_cycle_pushforward"
    ],
    [
      "实系数版本",
      "直接对实际 Cartier cycles 的有限实线性组合证明推出拉回等式。",
      "exists_realCartier_pullback_pushforward"
    ]
  ],
  "decl": "exists_realCartier_pullback_pushforward",
  "file": "CartierPushPull.lean",
  "deps": [
    "cartierpullback",
    "localcartier",
    "codimone"
  ],
  "related": [
    "proper_birational_weil_cycle_pushforward",
    "exists_cartierAtlas_pullback_pushforward",
    "cartierAtlas_real_sum_isWeilDivisor"
  ],
  "paper": "proper",
  "x": 278,
  "y": 3100
});
Object.assign(find("effdown"),{
  "title": "真实 R-Cartier 有效性下降",
  "status": "done",
  "statement": "构造实际拉回：若拉回 R-Cartier 除子的 Weil cycle 有效，则原除子的 Weil cycle 有效。",
  "scope": "实际推拉恒等式在证明内部建立，已不需要 hleft。拉回有效是应用时的数学条件，不是缺失的几何桥接；射影 negativity 给出这项条件的完整几何证明仍待完成。",
  "inputs": [
    "正规整、局部 Noetherian 概形间 proper birational f。",
    "D 是有限实线性组合的实际 Cartier 图册。",
    "应用下降时已知构造的拉回有效。"
  ],
  "steps": [
    [
      "构造拉回并证明恒等式",
      "复用实际 R-Cartier 拉回构造，内部证明 f_*(f*D)=D。",
      "exists_realCartier_pullback_pushforward"
    ],
    [
      "推出有效 cycle",
      "真实 cycle 推出保持非负系数，再用已证明的恒等式得到原除子有效。",
      "exists_realCartier_effectivity_descent"
    ]
  ],
  "decl": "exists_realCartier_effectivity_descent",
  "file": "CartierPushPull.lean",
  "deps": [
    "geomcycle",
    "pushpull"
  ],
  "related": [
    "scheme_effective_descends",
    "effective_descends"
  ],
  "paper": "proper",
  "x": 278,
  "y": 3100
});
find('negative').deps=['push','strict'];
find('negative').scope='系数推论已验证；strict 现已构造实际严格变换并证明 ExceptionalIndex 恰为像不在余维一的几何素点，模型可用于真实 Weil 除子。';
find('chow').deps=['hartshornegraph','modsurj','pushpull'];
find('chow').scope='实际 Cartier 拉回、Weil cycle、实系数推拉及有效性下降现已完成。按 Hartshorne 的有限仿射覆盖射影性、有限正规化以及曲线交数／支撑性质仍待完成。';
find('chow').inputs[2]='已完成：实际 R-Cartier 推拉与有效性下降。待完成：曲线射影公式、支撑拉回及有限正规化。';
find('localorder').scope='DVR 阶数与剩余域次数已验证；现在通过 actual Cartier atlas、函数域映射与严格变换完成几何系数识别和推拉。';
find('projection').scope+=' 实际 Cartier 方程拉回及 underlying Weil cycle 现已完成；完整曲线的线丛次数与交数兼容仍待完成。';

find('chow').steps[2][1]='有限正规化、曲线射影公式和支撑逆像仍待完成；实际 R-Cartier 拉回、推拉及有效性下降已经验证。';

find('fiberdown').scope='只完成集合层面的下降：假设改造满射、上方支撑等于逆像，并且上方每个纤维已满足二择一，才能推出下方结论。上方几何二择一及高维曲线步骤仍未完成；本节点不是完整的 Theorem 1.4(2) 证明。';

// Actual point-counting route: finite divisors are verified, global line bundles remain open.
nodes.push({
  "id": "affinedivisor",
  "title": "有限除子的逐点拉回与次数",
  "status": "done",
  "x": 536,
  "y": 3500,
  "deps": [
    "pointtensor",
    "principaldivisor"
  ],
  "decl": "affineDivisorPullback_degree",
  "file": "DivisorPullback.lean",
  "paper": "proper",
  "related": [
    "affineDivisorDegree_single",
    "affinePointDivisorPullback_degree",
    "affinePointDivisorPullback_apply",
    "affineDivisorPullback_apply",
    "affinePrincipalDivisor_pullback",
    "closedPoint_residueDegree_one",
    "algebraicallyClosed_point_pullback_count",
    "affineDivisorPullback_support",
    "affineDivisorPullback_effective_iff",
    "algebraicallyClosed_effective_divisor_degree_pos"
  ],
  "statement": "在实际有限仿射正规曲线映射下，点的张量长度重数延伸为任意有限带符号除子的拉回，并证明 deg(h*D)=[L:K]deg(D)。",
  "scope": "此处 deg 是有限除子的闭点次数和；还不是完整曲线上任意线丛的次数。无可分性或特征零限制。另已证明主除子拉回、支撑逆像和有效性等价。",
  "inputs": [
    "有限、无挠的实际 Dedekind 环扩张 R→S；平坦性从无挠性推出。",
    "R、S 是有限型 k-代数，K、L 是其实际分式域。",
    "闭点重数等于实际张量积长度；代数闭域下剩余域次数均为 1。"
  ],
  "steps": [
    [
      "从点到有限除子",
      "沿点生成元作加法延伸，允许任意正负整数系数。",
      "affineDivisorPullback_degree"
    ],
    [
      "核对局部方程",
      "由 ord_q(h*a)=e_q ord_p(a)，证明拉回主除子等于拉回函数的主除子。",
      "affinePrincipalDivisor_pullback"
    ],
    [
      "代数闭域下直接数重数",
      "Zariski 引理给每个闭点次数 1，原像点的张量长度总和就是 [L:K]，包含不可分次数。",
      "algebraicallyClosed_point_pullback_count"
    ],
    [
      "支撑与正性",
      "实际拉回支撑为原支撑的逆像；有效性保持并可下降，非零有效除子次数严格为正。",
      "affineDivisorPullback_effective_iff"
    ]
  ]
});
nodes.push({
  "id": "separablenorm",
  "title": "可分扩张的素理想范数",
  "status": "done",
  "x": 278,
  "y": 3650,
  "deps": [],
  "decl": "separable_prime_ideal_norm",
  "file": "SeparableNorm.lean",
  "paper": "proper",
  "statement": "有限可分 Dedekind 扩张中，N(P)=p^[k(P):k(p)]。底分式域无需 perfect。",
  "scope": "范数路线的辅助结果，要求扩张本身可分。逐点长度路线不使用这个要求；此结果也尚未构成完整曲线的乘积公式。",
  "inputs": [
    "有限、无挠 Dedekind 环扩张。",
    "分式域扩张可分；P、p 是实际满足 lying over 的极大理想。"
  ],
  "steps": [
    [
      "构造正规闭包",
      "在有限正规闭包中取整闭包，构造实际 Dedekind 环。"
    ],
    [
      "在 Galois 扩张中算范数",
      "应用已验证的素理想范数公式。"
    ],
    [
      "沿塔下降",
      "用范数传递性与剩余域次数乘法性，消去正规闭包的幂次。"
    ]
  ]
});
find('projection').deps.push('affinedivisor');
find('projection').steps[1]=['逐点计数与有限除子：已验证','以实际张量长度计原像点重数，再由加法延伸到所有有限带符号除子；主除子拉回兼容也已证明。','affineDivisorPullback_degree'];
find('projection').steps[2]=['完整曲线的线丛次数：待完成','局部可取仿射邻域；全局曲线仍须完整。建立任意线丛的除子表示及次数与表示无关，再接入正规化和像为点的情形。'];
find('projection').precise.zh.gap='已完成实际逐点张量长度、有限除子的可加拉回与次数公式、主除子拉回兼容，以及代数闭域下直接重数计数。尚需建立完整曲线任意线丛的除子表示和次数与表示选择无关，并接入正规化及像为点的情形。当前仍未删除几何 hcompat。';
find('projection').precise.en.gap='Actual tensor lengths, additive pullback and degree of finite divisors, principal-divisor compatibility, and direct multiplicity counting over an algebraically closed field are proved. Complete-curve divisor representations of arbitrary line bundles, representation-independent degree, normalization and the point-image case remain open. Geometric hcompat has not yet been removed.';
find('projection').inputs=['已验证：交换图拉回同构、点的张量长度、有限除子次数拉回公式及主除子兼容。','待完成：完整曲线的任意线丛与除子的对应、次数的表示无关、正规化及像为点时的次数。','主线采用逐点长度计数，含不可分情形；范数结果保留为辅助证明。'];

// Actual geometry: global normal isomorphisms, pointwise ZMT and effective Cartier support.
Object.assign(find('normalfinite'),{
  "title": "正规底上的有限双有理概形同构",
  "file": "FiniteNormalGeometry.lean",
  "decl": "finite_normal_birational_isIso",
  "deps": [
    "normalsections"
  ],
  "related": [
    "birationalMorphism_dominant",
    "birationalMorphism_generic_stalk_isIso",
    "dominantFunctionFieldMap_germ",
    "finite_normal_birational_affine_bijective",
    "normalStalks_restrict",
    "birationalMorphism_restrict",
    "proper_normal_birational_isIso_near_finite_fiber"
  ],
  "statement": "有限双有理态射 f:X→Y，X、Y 整且 Y 正规，则实际 f 是概形同构。有限纤维的 proper 双有理态射也在像点附近同构。",
  "scope": "由实际双有理同构开集构造泛点 stalk 同构及函数域嵌入；正规仿射环给坐标映射双射，再粘合为全局 Scheme 同构。原先的仿射化与粘合缺口已补齐。",
  "inputs": [
    "实际整概形 X、Y 及 BirationalMorphism f。",
    "IsFinite f；Y 的实际 stalk 整闭。",
    "有限纤维邻域推论要求 IsProper f 和该纤维的点集有限。"
  ],
  "steps": [
    [
      "构造实际函数域嵌入",
      "同构开集给泛点 stalk 的逆映射，将逆像开集的截面嵌入 Y 的实际函数域。",
      "birationalMorphism_generic_stalk_isIso"
    ],
    [
      "在每个仿射开集上证明",
      "有限性给整性，整闭性给坐标环映射满射；函数域嵌入给单射。",
      "finite_normal_birational_affine_bijective"
    ],
    [
      "全局粘合",
      "沿 Y 的所有仿射开集覆盖，用同构态射的 Zariski 局部性得到 IsIso f。",
      "finite_normal_birational_isIso"
    ],
    [
      "有限纤维附近",
      "先用 proper 的有限纤维邻域定理，再限制双有理性及正规性，应用全局同构结果。",
      "proper_normal_birational_isIso_near_finite_fiber"
    ]
  ]
});
nodes.push({
  "id": "zmtpoint",
  "title": "Zariski 主定理：准有限点附近同构",
  "status": "done",
  "x": 278,
  "y": 3800,
  "deps": [
    "normalfinite",
    "normalsections"
  ],
  "file": "FiniteNormalGeometry.lean",
  "decl": "proper_normal_birational_isIso_near_quasiFiniteAt",
  "related": [
    "birational_affine_functionField_embedding",
    "birational_relative_integralClosure_bijective",
    "normal_birational_fromNormalization_isIso",
    "exceptional_point_not_quasiFiniteAt",
    "exceptional_fiber_point_not_isOpen_singleton"
  ],
  "paper": "support",
  "statement": "正规底上的 proper 双有理映射，只要在一个原像点 x 准有限，就在 f(x) 的开邻域同构。因此每个 exceptional 纤维点都非孤立。",
  "scope": "点态结论已由实际相对正规化与 mathlib 的 Zariski 主定理证明，不再把它作为覆盖输入。此节点还没有构造纤维中的完整曲线。",
  "inputs": [
    "X、Y 是实际整概形，f 是 proper 且双有理。",
    "Y 的所有实际局部环整闭。",
    "邻域定理输入是 f.QuasiFiniteAt x；exceptional 推论用像点不属于同构开集来定义 center。"
  ],
  "steps": [
    [
      "识别相对正规化",
      "在每个仿射开集的截面环中，双有理嵌入与整闭性给 integralClosure(R,Γ(f⁻¹U))=R；全局粘合。",
      "normal_birational_fromNormalization_isIso"
    ],
    [
      "应用点态 Zariski 主定理",
      "mathlib 给 toNormalization 在指定准有限点附近的同构。相对正规化已经是 Y，将此邻域送回 Y。",
      "proper_normal_birational_isIso_near_quasiFiniteAt"
    ],
    [
      "逐点排除准有限",
      "exceptional 的像不属于任何同构开集，故该点不准有限。",
      "exceptional_point_not_quasiFiniteAt"
    ],
    [
      "实际纤维非孤立",
      "用准有限与实际纤维中单点开集的等价，证明每个 exceptional 纤维点的单点集都不是开集。",
      "exceptional_fiber_point_not_isOpen_singleton"
    ]
  ]
});
nodes.push({
  "id": "cartiersupport",
  "title": "有效 Cartier 支撑拉回与下降",
  "status": "done",
  "x": 536,
  "y": 3950,
  "deps": [
    "cartierpullback",
    "modsurj",
    "setdown"
  ],
  "file": "CartierSupport.lean",
  "decl": "exists_effective_cartierAtlas_pullback_support",
  "related": [
    "rationalUnitAt_unit_transition",
    "cartierAtlas_support_eq_on_chart",
    "rationalUnitAt_regular_iff",
    "rationalUnitAt_regular_pullback_iff",
    "effective_cartierAtlas_weil_nonneg",
    "exists_effective_cartierAtlas_fiber_descent"
  ],
  "paper": "proper",
  "statement": "实际有效 Cartier 拉回保持有效，且 Supp(p*D)=p⁻¹(Supp D)。proper 双有理改造下，两边纤维的支撑二择一互相等价。",
  "scope": "用实际局部环中的正则方程和单位来定义有效性及支撑，证明转换图册不改变支撑。这里只完成有效 Cartier 情形；一般有效 R-Cartier 的支撑识别仍待完成，也没有证明每个纤维必满足二择一。",
  "inputs": [
    "实际整概形之间的 dominant 映射 p，以及有效 CartierAtlas A。",
    "Effective 表示每个局部有理方程都来自实际局部环的正则元素。",
    "下降推论另外要求 p proper 且双有理；满射与支撑等式均由几何证明。"
  ],
  "steps": [
    [
      "定义真实支撑",
      "局部方程不为局部环单位的点构成支撑；单位转换函数保证与图册选择无关。",
      "cartierAtlas_support_eq_on_chart"
    ],
    [
      "局部拉回反映单位",
      "实际 Scheme stalkMap 是局部环同态，正则元素拉回为单位当且仅当原元素是单位。",
      "rationalUnitAt_regular_pullback_iff"
    ],
    [
      "构造有效拉回",
      "把正则方程沿实际 stalkMap 拉回，输出有效 CartierAtlas 及完整支撑逆像等式。",
      "exists_effective_cartierAtlas_pullback_support"
    ],
    [
      "接到实际纤维下降",
      "proper 双有理给满射；代入已证明的支撑逆像，纤维不相交／包含在上下两边等价。仍须另证上方二择一。",
      "exists_effective_cartierAtlas_fiber_descent"
    ]
  ]
});
find('cover').deps=['zmtpoint'];
find('cover').scope='点态同构判据与每个 exceptional 纤维点非孤立已完成。剩余是把非孤立闭点接为正维纤维分量，并实际构造经过该点的完整曲线；不能把非孤立结论直接标成曲线已存在。';
find('cover').inputs=['已完成：正规底上的 proper 双有理映射在任一准有限点的像附近同构，故每个 exceptional 纤维点非孤立。','待完成：在包含指定闭点的正维射影纤维分量中，用超平面实际截出完整曲线。'];
find('cover').steps[1]=['点态 Zariski 主定理：已验证','相对正规化在正规底上就是底；mathlib 的准有限点邻域同构因此给原态射的目标同构邻域。','proper_normal_birational_isIso_near_quasiFiniteAt'];
find('cover').steps[2]=['每个 exceptional 纤维点非孤立：已验证','准有限等价于实际纤维中的单点开集；逐点排除准有限，得到每个单点都非开。正维分量与曲线构造仍待接入。','exceptional_fiber_point_not_isOpen_singleton'];
find('fiberdown').deps.push('cartiersupport');
find('fiberdown').related=['exists_effective_cartierAtlas_fiber_descent'];
find('fiberdown').scope='集合下降逻辑已验证，实际有效 Cartier 情形的满射和支撑逆像也已由几何证明。仍须完成上方纤维二择一，以及一般有效 R-Cartier 的支撑识别；完整 negativity lemma 未完成。';
find('fiberdown').inputs=['已完成：proper 双有理改造满射。','已完成：有效 Cartier 的实际支撑拉回及纤维下降。待完成：一般有效 R-Cartier。','仍待完成：上方每个纤维的支撑二择一；不能把它当作已经证明。'];
find('fiberdown').steps=[['实际 Cartier 支撑：已验证','构造有效拉回及完整支撑逆像等式，不再把该等式作为 Cartier 情形的输入。','exists_effective_cartierAtlas_pullback_support'],['上下纤维等价：已验证','proper 双有理改造满射，给上下纤维的支撑二择一等价。','exists_effective_cartierAtlas_fiber_descent'],['尚待接通','完成上方的纤维二择一证明及一般有效 R-Cartier 支撑识别。']];
find('chow').deps.push('cartiersupport');
find('chow').scope='Hartshorne 图像闭包、实际 Cartier 拉回、实系数推拉与有效性下降均已完成；有效 Cartier 的支撑拉回现已完成。有限覆盖的射影性、有限正规化、全局曲线交数和一般有效 R-Cartier 支撑仍待完成。';
find('chow').inputs[2]='已完成：实际 R-Cartier 推拉与有效性下降、有效 Cartier 支撑逆像。待完成：全局曲线射影公式、一般有效 R-Cartier 支撑以及有限正规化。';
find('chow').steps[2][1]='有效 Cartier 支撑逆像和实际 R-Cartier 推拉已验证；有限正规化、全局曲线交数和一般有效 R-Cartier 支撑仍待完成。';

// Proven R-coefficient algebra and actual Cartier / Weil decomposition.
nodes.push({
  "id": "rcone",
  "title": "实系数有效分解：有理锥与清分母",
  "status": "done",
  "x": 278,
  "y": 4100,
  "deps": [],
  "file": "RationalCone.lean",
  "decl": "effective_integral_coefficient_decomposition",
  "related": [
    "open_set_mem_convexHull_rational",
    "open_set_exists_rational_convex_combination",
    "positive_rational_coefficient_decomposition",
    "rational_parameterization_preserves_zero",
    "rationalCoefficientMap_cast",
    "rationalCoefficientMap_comp_zero",
    "effective_rational_coefficient_decomposition",
    "rational_vector_positive_integer_multiple"
  ],
  "paper": "proper",
  "statement": "有理矩阵 M 与实系数 x 若满足 Mx≥0，则 x=Σwⱼzⱼ，wⱼ≥0、zⱼ为整数向量、Mzⱼ≥0；Mx 为零的位置在每个 Mzⱼ中仍为零。",
  "scope": "有限系数定理已证明：精确分解、零系数约束及正清分母均为结论，不是额外输入。这里还没有把非负 Weil 系数转成 Cartier 的正则局部方程。",
  "inputs": [
    "有限个有理系数生成元及有限个素系数位置。",
    "原实组合的所有系数非负；不要求原组合的各个实权重非负。"
  ],
  "steps": [
    [
      "保持所有零系数",
      "用实坐标的有限有理张成空间取基，构造自动满足原有零系数等式的有理参数族。",
      "rational_parameterization_preserves_zero"
    ],
    [
      "有理开锥",
      "用有理长方体顶点证明每个开集中的点都属于该开集内有理点的凸包。",
      "open_set_mem_convexHull_rational"
    ],
    [
      "精确有效分解",
      "只在原正系数位置施加严格正条件，在零位置保持等式；得到有理有效组合。",
      "effective_rational_coefficient_decomposition"
    ],
    [
      "正清分母",
      "取各有理分母的正乘积，调整实权重，把有理组合变成整数组合。",
      "effective_integral_coefficient_decomposition"
    ]
  ],
  "upstream": [
    [
      "Chen–Moriwaki · Proposition 2.4.16",
      "https://webusers.imj-prg.fr/~huayi.chen/Recherche/adelic_curve.pdf#page=175"
    ]
  ]
});
nodes.push({
  "id": "rdecomp",
  "title": "真实 R-Cartier：非负 Weil 系数分解",
  "status": "done",
  "x": 536,
  "y": 4100,
  "deps": [
    "rcone",
    "localcartier"
  ],
  "file": "RealCartierDecomposition.lean",
  "decl": "exists_realCartier_nonnegative_weil_decomposition",
  "related": [
    "dvr_rationalOrder_zpow",
    "dvr_rationalOrder_prod",
    "exists_cartierAtlas_integralCombination",
    "exists_cartierAtlas_integralCombination_coefficients"
  ],
  "paper": "proper",
  "statement": "正规准紧概形上，有效的 R-Cartier Weil cycle 可写成非负实权重的实际 Cartier 图册组合；每个图册的 Weil 系数非负，并且原零系数仍为零。",
  "scope": "从真实局部方程构造整数组合，核验真实 Weil 系数及加权 cycle 等式。尚须证明非负 Weil 系数使局部方程正则，才能接到有效 R-Cartier 的完整支撑拉回。完整 negativity lemma 仍未完成。",
  "inputs": [
    "实际整、局部 Noetherian、准紧概形，所有实际 stalk 整闭。",
    "有限个实际 CartierAtlas 与任意实权重。",
    "原真实 Weil cycle 有效；不要求单个 Cartier 图册或原实权重有效。"
  ],
  "steps": [
    [
      "构造实际整数组合",
      "把有限组图册的开集共同细分为仿射邻域；方程为整数次幂之积，单位转换函数也实际构造。",
      "exists_cartierAtlas_integralCombination"
    ],
    [
      "核验真实系数",
      "真实 DVR 赋值在方程乘积及整数次幂下分别相加及相乘，得到实际 Weil 系数等式。",
      "exists_cartierAtlas_integralCombination_coefficients"
    ],
    [
      "接入有效分解",
      "各图册的有限 Weil 支撑构成有限系数矩阵。应用有理锥分解，再构造相应实际 Cartier 图册。",
      "exists_realCartier_nonnegative_weil_decomposition"
    ],
    [
      "剩余几何桥接",
      "非负 Weil 系数 ⇒ 局部方程正则；需正规 Noetherian 域的余维一延拓定理。完成后再识别全支撑与拉回。"
    ]
  ],
  "upstream": [
    [
      "Chen–Moriwaki · Proposition 2.4.6",
      "https://webusers.imj-prg.fr/~huayi.chen/Recherche/adelic_curve.pdf#page=170"
    ],
    [
      "Stacks · normal Noetherian height-one intersection",
      "https://stacks.math.columbia.edu/tag/031T"
    ]
  ]
});
find('fiberdown').deps.push('rdecomp');
find('fiberdown').scope='有效 Cartier 的实际支撑拉回已完成；一般 R-Cartier 的有理锥分解、实际整数组合与非负 Weil 系数分解也已完成。仍缺非负 Weil 系数到正则局部方程的延拓、完整支撑识别，以及上方纤维二择一；完整定理尚未完成。';
find('fiberdown').inputs[1]='已完成：有效 Cartier 支撑拉回，以及实际 R-Cartier 的非负 Weil 系数分解。待完成：非负 Weil 系数到正则局部方程及全支撑识别。';
find('fiberdown').steps[2]=['R-Cartier 分解：已验证','已构造非负 Weil 系数的实际 Cartier 图册分解，原零系数保持为零。','exists_realCartier_nonnegative_weil_decomposition'];
find('fiberdown').steps.push(['尚待接通','证明非负 Weil 系数对应正则局部方程及完整支撑，并完成上方纤维二择一。']);
find('chow').deps.push('rdecomp');
find('chow').scope='有效 Cartier 支撑拉回、实际 R-Cartier 推拉及非负 Weil 系数分解已完成。有限覆盖的射影性、有限正规化、全局曲线交数、非负 Weil 系数的局部延拓与一般 R-Cartier 全支撑仍待完成。';

nodes.push({
  "id": "normalext",
  "title": "正规环的余维一延拓",
  "decl": "normal_fraction_regular_iff_height_one",
  "file": "NormalExtension.lean",
  "deps": [],
  "status": "done",
  "x": 278,
  "y": 4400,
  "paper": "proper",
  "statement": "正规 Noetherian 整环 R 中，分式在每个高度一素理想处正则，当且仅当它属于 R。",
  "scope": "环论延拓定理已证明。伴随素理想高度一及局部 DVR 均由证明推出，没有把余维一交集等式作为输入；适用于任意特征。",
  "inputs": [
    "实际正规 Noetherian 整环及其分式域。",
    "分式在所有高度一素理想局部化处正则。"
  ],
  "steps": [
    [
      "行列式技巧",
      "在正规局部环中用主理想商的消去子构造分式；积分性与非稳定情形给出主最大理想。",
      "normal_local_annihilator_maximal_isPrincipal"
    ],
    [
      "伴随素理想",
      "在实际伴随素理想处局部化，证明该局部环为 DVR，从而高度恰为一。",
      "normal_principal_associated_prime_height_one"
    ],
    [
      "整除检测",
      "若整除失败，主理想商中一个非零类产生高度一伴随素理想，和该处整除矛盾。",
      "normal_divisibility_of_height_one_local"
    ],
    [
      "分式延拓",
      "选择真实分子分母，由高度一整除准则证明分式属于原环。",
      "normal_fraction_regular_iff_height_one"
    ]
  ],
  "related": [
    "normal_local_annihilator_maximal_isPrincipal",
    "normal_local_associated_principal_maximal_isPrincipal",
    "normal_local_associated_principal_isDVR",
    "normal_principal_associated_prime_isDVR",
    "normal_principal_associated_prime_height_one",
    "normal_divisibility_of_height_one_local",
    "normal_fraction_regular_of_height_one_denominators"
  ],
  "upstream": [
    [
      "Stacks · normal height-one intersection",
      "https://stacks.math.columbia.edu/tag/031T"
    ]
  ]
});

nodes.push({
  "id": "cartiereff",
  "title": "真实 Cartier 有效性：Weil 系数判据",
  "decl": "cartierAtlas_effective_iff_weil_nonneg",
  "file": "CartierEffectivity.lean",
  "deps": [
    "normalext",
    "localcartier"
  ],
  "status": "done",
  "x": 278,
  "y": 4400,
  "paper": "proper",
  "statement": "正规局部 Noetherian 概形上，实际 Cartier 图册有效，当且仅当其所有真实 Weil 系数非负。",
  "scope": "DVR 非负阶数、仿射开集的余维一延拓及实际 stalk 方程正则均已证明。有效性由这些证明推出，不再作为几何桥接输入。",
  "inputs": [
    "实际整且局部 Noetherian 的概形，所有实际 stalk 整闭。",
    "真实 Cartier 图册及其实际 Weil cycle。"
  ],
  "steps": [
    [
      "DVR 正则性",
      "非负分式阶数等价于分母整除分子，得到实际局部环元素。",
      "dvr_rationalOrder_nonneg_iff_regular"
    ],
    [
      "实际仿射延拓",
      "在真实仿射坐标环上应用余维一延拓，局部化就是实际 Scheme stalk。",
      "normal_affine_rational_regular"
    ],
    [
      "有效性等价",
      "Weil 非负性使所有图册方程在每个 stalk 正则；反向由 DVR 阶数给出。",
      "cartierAtlas_effective_iff_weil_nonneg"
    ]
  ],
  "related": [
    "dvr_rationalOrder_nonneg_iff_regular",
    "normal_affine_rational_regular"
  ]
});

nodes.push({
  "id": "geomsupport",
  "title": "真实 Cartier 全支撑与实组合拉回",
  "decl": "exists_realCartier_decomposition_support_pullback",
  "file": "CartierVanishing.lean",
  "deps": [
    "cartiereff",
    "rdecomp",
    "cartiersupport"
  ],
  "status": "done",
  "x": 278,
  "y": 4400,
  "paper": "proper",
  "statement": "Cartier 全支撑等于实际 Weil 非零素分量的闭包；有效实组合的支撑是正权重项支撑的并集，所构造分解的拉回支撑是逆像。",
  "scope": "实际单位邻域、全支撑闭性、余维一闭包、正权重实组合及分解的支撑拉回均已证明。仍需把该分解的拉回与原 R-Cartier 表示的逐项拉回核对；上方纤维二择一仍未完成。",
  "inputs": [
    "实际整、正规、局部 Noetherian 概形及 dominant 态射。",
    "任意原实权重，但原实际 Weil 组合有效；构造分解时底概形准紧。"
  ],
  "steps": [
    [
      "识别全支撑",
      "局部单位延拓为邻域单位截面；零阶数同时延拓方程与其逆，识别所有余维的支撑。",
      "cartierAtlas_vanishingSupport_eq_closure_weilSupport"
    ],
    [
      "正权重并集",
      "有效 Cartier 系数非负，不会相消；有限并与闭包交换。",
      "effective_cartier_real_sum_support"
    ],
    [
      "实际拉回",
      "构造每个有效 Cartier 的真实拉回；局部态射反映单位，得到实组合支撑逆像。",
      "exists_effective_real_sum_pullback_support"
    ],
    [
      "任意实表示",
      "先构造有效 Cartier 分解，再拉回该分解。原表示逐项拉回的兼容及上方二择一仍待完成。",
      "exists_realCartier_decomposition_support_pullback"
    ]
  ],
  "related": [
    "rationalUnitAt_exists_affine_unit_section",
    "rationalUnitAt_isOpen",
    "cartierAtlas_vanishingSupport_isClosed",
    "normal_affine_rationalUnitAt_of_orders_zero",
    "cartierAtlas_vanishingSupport_eq_closure_weilSupport",
    "effective_cartier_real_sum_support",
    "exists_effective_real_sum_pullback_support"
  ]
});

find('rdecomp').title='真实 R-Cartier：有效 Cartier 分解';
find('rdecomp').file='CartierEffectivity.lean';
find('rdecomp').decl='exists_realCartier_effective_weil_decomposition';
find('rdecomp').related=['exists_realCartier_nonnegative_weil_decomposition','exists_cartierAtlas_integralCombination','exists_cartierAtlas_integralCombination_coefficients'];
find('rdecomp').deps.push('cartiereff');
find('rdecomp').statement='原实际 Weil 实组合有效时，可构造非负实权重的实际有效 Cartier 图册分解，精确保持加权 Weil cycle 和原零系数。';
find('rdecomp').scope='有理锥分解、整数组合、实际 Weil 系数及 Cartier 方程正则均已证明。等式为构造的实际 Weil cycle 等式；完整 negativity lemma 仍未完成。';
find('rdecomp').steps[3]=['实际 Cartier 有效性：已证明','应用已证明的余维一延拓，把非负 Weil 系数转成正则局部方程。','cartierAtlas_effective_iff_weil_nonneg'];
find('fiberdown').deps.push('geomsupport');
find('fiberdown').scope='实际 Cartier 有效性、有效实组合的全支撑及所构造分解的支撑拉回已完成。仍缺分解拉回与原表示逐项拉回的兼容，以及上方纤维二择一；完整定理尚未完成。';
find('fiberdown').inputs[1]='已完成：实际有效 Cartier 分解、全支撑闭包及分解的支撑拉回。待完成：与原表示逐项拉回兼容。';
find('fiberdown').steps[2]=['有效 R-Cartier 分解：已验证','所有构造的 Cartier 项的局部方程均正则，实际 Weil cycle 等式已证明。','exists_realCartier_effective_weil_decomposition'];
find('fiberdown').steps[3]=['所构造分解的全支撑拉回：已验证','支撑识别为 Weil 非零素分量的闭包，再证明分解拉回的支撑等于逆像。','exists_realCartier_decomposition_support_pullback'];
find('fiberdown').steps.push(['尚待接通','与原表示逐项拉回兼容，并完成上方纤维二择一。']);
find('chow').deps.push('geomsupport');
find('chow').scope='实际 R-Cartier 推拉、有效 Cartier 分解、全支撑识别及分解的支撑拉回已完成。仍缺有限覆盖的射影性、有限正规化、全局曲线交数、与原实表示逐项拉回兼容及上方纤维二择一。';
