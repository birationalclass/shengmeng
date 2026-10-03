export const statusLabels = {done:'✓ Lean 已验证',conditional:'◐ 条件式证明 · 输入未齐',assumption:'? 暂作假设',pending:'○ 待完成目标'};
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

// Actual original-presentation pullback: formal-18
find('geomsupport').file='RealCartierPullback.lean';
find('geomsupport').decl='exists_realCartier_termwise_pullback_support';
find('geomsupport').statement='原实权重可为负；只要真实 Weil 实组合有效，其原表示的实际逐项拉回有效，且全支撑恰为原全支撑的逆像。';
find('geomsupport').scope='原表示逐项拉回与有效分解拉回的系数兼容已证明，包括例外除子映到高余维中心的情形。实际有效性、全支撑闭包及支撑逆像全部完成；没有证明上方纤维必然二择一。';
find('geomsupport').steps[3]=['原表示逐项拉回：已验证','保留原系数坐标及局部方程乘积；拉回实际单位后计算源空间 DVR 阶数，证明两个拉回的实际 Weil cycle 相同。','exists_realCartier_termwise_pullback_support'];
find('geomsupport').steps.push(['例外除子的系数','底点不必余维一：使用该点真实 stalk 单位拉回，再在源空间余维一处计算系数。','cartierAtlas_pullback_integralCombination_coefficients']);
find('geomsupport').related.push('exists_realCartier_decomposition_support_pullback');
find('rdecomp').related.push('exists_realCartier_effective_decomposition_equations');
find('rdecomp').scope='真实有效 Cartier 分解及原零系数保持已证明；增强版本还保留原系数坐标等式及实际局部方程乘积，因此可与原实表示逐项拉回核对。完整 negativity lemma 仍未完成。';
find('fiberdown').status='done';
find('fiberdown').file='RealCartierPullback.lean';
find('fiberdown').decl='exists_realCartier_termwise_fiber_descent';
find('fiberdown').title='真实 R-Cartier 纤维支撑下降';
find('fiberdown').statement='proper birational 改造下，原有效 R-Cartier 表示的实际逐项拉回有效，且纤维支撑二择一在上下空间等价。';
find('fiberdown').scope='实际 Scheme 满射、原表示逐项拉回、有效性、全支撑逆像及二择一的下降等价均已证明。此节点不证明上方二择一成立；完整定理尚未完成。';
find('fiberdown').inputs=['实际正规整且局部 Noetherian 概形；底概形准紧；proper birational 改造。','原真实 R-Cartier 有限表示及任意实权重，其实际 Weil 实组合有效。','输出是上下空间的二择一等价；上方二择一成立仍需独立几何证明。'];
find('fiberdown').steps=[
 ['构造原表示拉回','逐项构造真实 Cartier 拉回，保留实际局部方程。','exists_cartierAtlas_pullback'],
 ['兼容有效分解','用原系数坐标和局部方程乘积计算源空间系数，证明逐项拉回等于有效分解拉回。','cartierAtlas_pullback_integralCombination_coefficients'],
 ['全支撑逆像','真实有效性和所有余维的支撑逆像已证明，不再作为输入。','exists_realCartier_termwise_pullback_support'],
 ['实际下降','由 proper birational 的实际满射反映支撑不交和包含，得到二择一等价。','exists_realCartier_termwise_fiber_descent'],
 ['剩余独立问题','上方纤维必然二择一的几何证明仍未完成；本节点只证明下降等价。']
];
find('fiberdown').related=['exists_realCartier_termwise_pullback_support','proper_birational_surjective','fiber_dichotomy_descends'];
find('fiberdown').deps=['geomsupport','modsurj','setdown'];
find('chow').scope='实际 R-Cartier 推拉、有效分解、原表示逐项拉回的有效性与全支撑逆像，以及二择一下降等价已完成。仍缺有限覆盖的射影性、有限正规化、全局曲线交数及上方纤维二择一。';
find('geomsupport').related.push('dominantFunctionFieldMap_stalk_unit','cartierAtlas_pullback_coefficient_eq','cartierAtlas_integralCombination_coefficients','exists_realCartier_effective_decomposition_equations','cartierAtlas_pullback_integralCombination_coefficients','realWeightedWeilCycle_eq_of_integral_coefficients','exists_effective_cartierAtlas_pullback_data');

// Direct divisor/local-order route: formal-19
Object.assign(find("separablenorm"),{"title": "实际范数与主除子推出", "file": "NormDivisor.lean", "decl": "separable_functionField_principal_norm", "related": ["separable_prime_ideal_norm", "separable_relNorm_factorization", "ideal_primePower_multiplicity", "ideal_primePower_product_multiplicity", "normalizedIdealPoints_asIdeal", "separable_ideal_norm_order", "heightOneOrder_regular_eq_multiplicity", "separable_integral_norm_order", "ideal_order_eq_point_count", "idealFactorDivisor_apply", "idealFactorDivisor_principal", "affineDivisorPushforward_single", "separable_ideal_norm_divisor", "fractionFieldNormUnits_integral", "separable_integral_principal_norm", "separable_affine_principal_norm", "affineDivisorPushforward_degree", "separable_affine_principal_norm_degree", "fractionRing_separable_of_fractionFields", "separable_integral_functionField_norm", "separable_functionField_principal_norm_degree"], "statement": "有限可分 Dedekind 扩张中，div(N(a))=h_*div(a)；范数与实际局部阶数、剩余域次数相容。", "scope": "实际理想范数、整元素及任意函数域单位的主除子公式均已证明。要求扩张本身可分，不要求底分式域 perfect。任意特征允许；不可分拉回的逐点长度公式另已证明。", "inputs": ["实际有限无挠 Dedekind 环扩张及可分函数域扩张。", "非零函数及真实 height-one 素点；推出权重为剩余域次数。"], "steps": [["实际理想范数", "证明素理想幂的阶数、范数可乘性及整元素范数公式。", "separable_integral_principal_norm"], ["延伸到分式", "将函数写成非零整元素的商，以可加阶数延伸。", "separable_affine_principal_norm"], ["真实函数域", "通过实际分式域同构和范数相容得到函数域主除子公式。", "separable_functionField_principal_norm"], ["取次数", "证明实际推出保持剩余域加权次数。", "separable_functionField_principal_norm_degree"]]});
Object.assign(find("ratproduct"),{"title": "P¹ 的实际主除子次数零", "file": "RationalDivisor.lean", "decl": "rational_actual_principal_degree_zero", "related": ["polynomial_factor_degree_sum", "rationalInfinityOrder_eq", "rationalFunction_principal_degree_zero", "polynomial_point_residueDegree", "polynomial_prime_principal_divisor", "polynomial_prime_principal_degree", "polynomial_principal_degree", "rational_affine_principal_degree"], "statement": "实际 k[t] 素点的主除子加权次数，加真实无穷远赋值阶数，等于 0。", "scope": "有限处使用实际素点、DVR 阶数及剩余域次数，不只是形式上的因子次数和。任意底域与任意特征适用。实际无穷远 DVR 的归一化也已证明。", "inputs": ["k 为任意域，a∈k(t) 非零。", "次数使用实际 prime-point Finsupp 及 quotient residue-field finrank。"], "steps": [["点的次数", "证明不可约素点的剩余域次数等于多项式次数。", "polynomial_point_residueDegree"], ["有限处主除子", "实际素点阶数和等于有理函数 intDegree。", "rational_affine_principal_degree"], ["无穷远相消", "真实无穷远赋值的负 intDegree 与有限处相消。", "rational_actual_principal_degree_zero"]]});
Object.assign(find("intersection"),{"deps": ["relativesigns", "cartiercurve"], "scope": "已从实际 Cartier 局部方程构造有限阶数和、非 dominant 曲线限制及有效除子的非负／严格正性；实系数有效分解也已接通。尚需实际完整曲线的主除子次数零及表示无关、任意实表示的线性和几何 f-ample 正性。没有把几何 ample 改定义成数值条件。", "inputs": ["已证明：实际有效 Cartier 限制的阶数和非负；支撑相交时严格正。有效实分解亦有同样符号。", "待证明：完整曲线上的主除子次数零接到 Scheme 闭点，从而证明主除子移动及任意表示不改变次数。", "C 为被 f 压缩的完整曲线；f-nef 的数值符号是定义。几何 f-ample 的次数严格正仍须接通。"], "steps": [["实际限制与阶数：已验证", "曲线不要求 dominant；限制使用真实局部单位与 stalk 映射。", "effective_cartier_restriction_order_signs"], ["实系数有效分解：已验证", "从任意原实权重构造正权重有效 Cartier 分解并限制到曲线。", "effective_realCartier_curve_decomposition_order_signs"], ["曲线在支撑内：移动已验证", "减去一个实际局部方程的主除子，移开泛点后构造限制。次数的移动无关性仍待完成。", "exists_moved_cartier_curve_restriction"], ["仍待接通", "完整曲线的主除子次数与表示无关，以及几何 f-ample 的严格正次数。"]]});
Object.assign(find("projection"),{"deps": ["geomcycle", "realspan", "pullbackdiagram", "localprojection", "principaldivisor", "pointtensor", "affinedivisor", "functionproduct", "cartiercurve"], "scope": "采用用户确认的直接除子与局部阶数路线。实际有限除子拉回、范数／赋值乘积公式、非 dominant Cartier 曲线限制与主除子移动已证明。还需把构造的赋值点识别为实际完整正规曲线闭点，证明移动／表示无关及全局拉回次数，接入正规化和像为点的零次数。完整几何投影公式仍未通过。", "inputs": ["已验证：真实点张量长度、有限除子次数拉回、主除子兼容、函数域范数／赋值公式。", "已验证：实际 Cartier 曲线限制、有限局部阶数和、有效性符号及主除子移动。", "仍缺：Scheme 完整曲线闭点与构造赋值点的识别、主除子移动无关性、全局次数拉回及像为点的零值。"], "steps": [["交换图：已验证", "模层拉回同构及直接 Cartier 限制已构造。", "curve_square_pullback_iso"], ["逐点计数：已验证", "实际张量长度给出有限除子公式，包含不可分次数。", "affineDivisorPullback_degree"], ["范数与赋值：已验证", "构造有限处及无穷远的整闭包，证明函数域主除子乘积公式。", "functionField_principal_degree_zero"], ["实际 Cartier 限制：已验证", "移动局部方程避开曲线泛点，并构造限制的实际方程。", "exists_moved_cartier_curve_restriction"], ["全局几何：待完成", "将赋值点接到完整曲线闭点，证明次数与移动无关及拉回次数公式，再处理正规化和点像。"]]});
nodes.push({"id": "cartiercurve", "title": "实际 Cartier 曲线限制与阶数正性", "status": "done", "x": 278, "y": 4650, "deps": ["geomsupport", "rdecomp", "localcartier"], "decl": "effective_realCartier_curve_decomposition_order_signs", "related": ["effective_real_cartier_curve_order_signs", "cartierOrderDivisor_apply", "cartierTotalOrder_eq_of_unit_transitions", "effective_cartierTotalOrder_nonneg", "effective_cartierTotalOrder_pos", "effective_cartierTotalOrder_pos_of_support", "stalkSpecialization_functionField", "generic_stalkMap_commutes", "exists_cartierAtlas_nondominant_pullback", "exists_effective_nondominant_cartier_pullback", "effective_cartier_restriction_order_signs", "cartierAtlas_move_off_generic_curve", "cartierAtlas_rationalTwist_transition", "exists_moved_cartier_curve_restriction"], "file": "RealCartierCurveDegree.lean", "paper": "projective", "statement": "以真实局部方程限制 Cartier 除子并求有限阶数和；有效限制非负，相交则严格正。构造的有效实分解也满足这些符号。", "scope": "使用真实 Scheme stalk 及 DVR 阶数，不假定曲线到环境空间 dominant 或交数非负。原实权重可为负。曲线原本包含在支撑中时，先用实际主除子移动构造限制。次数与移动／任意实表示无关及几何 ample 正性尚未证明。", "inputs": ["实际整曲线 C、整环境 X 及任意 Scheme 态射；阶数和要求 C 正规、局部 Noetherian、准紧。", "有效性正性要求 C 不被支撑包含；实情形使用已构造的有效分解。", "任意 Cartier 的移动限制不要求避开原支撑；此处不声称移动后的次数已证明与选择无关。"], "steps": [["真实次数", "有限支撑的实际 Cartier 系数给出局部阶数和。", "cartierOrderDivisor_apply"], ["非 dominant 限制", "泛点局部单位沿真实 stalk 映射构造曲线方程和过渡。", "exists_cartierAtlas_nondominant_pullback"], ["有效性与全支撑", "构造正规局部方程，证明支撑正好是逆像。", "exists_effective_nondominant_cartier_pullback"], ["正性", "真实非负阶数有限求和；支撑非空给至少一个正阶数。", "effective_cartier_restriction_order_signs"], ["任意原实权重", "使用已验证的有效分解，再限制正权重项。", "effective_realCartier_curve_decomposition_order_signs"], ["主除子移动", "减去一个实际局部方程，移开曲线泛点后限制；保留过渡单位。", "exists_moved_cartier_curve_restriction"]]},{"id": "functionproduct", "title": "函数域范数／赋值乘积公式", "status": "done", "x": 278, "y": 4800, "deps": ["ratproduct", "separablenorm"], "decl": "functionField_principal_degree_zero", "related": ["normalized_discrete_valuation_eq", "rational_infinity_normalized_valuation", "rational_infinity_heightOneOrder", "separable_infinity_principal_norm", "twoChart_principal_degree_zero"], "file": "FunctionFieldProductFormula.lean", "paper": "proper", "statement": "有限可分 L/k(t) 中，构造有限处与无穷远的实际整闭包，其主除子总阶数加权和为零。", "scope": "整闭包、有限性、Dedekind 性、真实归一化 DVR 赋值和范数等式都已证明。任意特征适用；要求所选参数给出可分扩张。无穷远剩余域与 k 的识别及这些赋值点与给定完整 Scheme 曲线的识别仍需几何证明。", "inputs": ["实际函数域 L 是 k(t) 的有限可分扩张；底域不必特征 0。", "整闭包及有限性是构造结果，不是输入的有限图表存在假设。"], "steps": [["构造整闭包", "有限处取 k[t] 在 L 中的整闭包；无穷远取实际 infinity DVR 在 L 中的整闭包。"], ["归一化无穷远赋值", "证明实际 DVR 的归一化赋值等于 inftyValuation。", "rational_infinity_normalized_valuation"], ["沿范数计数", "有限处及无穷远的范数局部阶数公式相加。", "twoChart_principal_degree_zero"], ["得到零", "用 P¹ 的实际次数零推出构造赋值点的主除子总和为零。", "functionField_principal_degree_zero"]]});
find("projection").precise.zh.gap="采用直接除子与局部阶数。有限除子拉回、构造函数域的范数／赋值乘积公式、真实非 dominant Cartier 限制及移动已证明。仍需实际完整曲线闭点与赋值点识别、移动／表示无关、正规化及像为点的零次数；完整投影公式尚未通过。";
find("projection").precise.en.gap="The route uses divisors and local orders directly. Finite-divisor pullback, the constructed function-field norm/valuation product formula, actual non-dominant Cartier restriction and moving are proved. Actual complete-curve place identification, degree independence under moves/presentations, normalization and point-image degree zero remain open. The full projection formula is not proved.";

// Actual Hartshorne I.6 correspondence and infinity residues: formal-20
nodes.push({"id": "infinityresidue", "title": "无穷远剩余域与实际底域次数", "statement": "k(t) 的实际无穷远 DVR 的剩余域就是 k；代数闭底域上，构造的无穷远素点剩余域次数均为一。", "scope": "通过首项相消证明每个无穷远正则函数模极大理想等于一个常数，构造真实剩余域同构。有限处和无穷远的次数权重现统一在同一底域 k 上；无穷远环不要求是有限生成 k-代数。", "inputs": ["k 任意域；无穷远环为实际 inftyValuation 的赋值子环。", "无穷远整闭包上的权重一结论使用 IsAlgClosed k；任意特征允许。"], "steps": [["常数逼近", "首项相消使差具有正无穷远阶数。", "rational_infinity_approximate_constant"], ["真实剩余域", "证明常数到实际剩余域的环映射双射。", "rational_infinity_residue_constants_bijective"], ["统一底域权重", "用真实剩余域次数塔将局部推出系数转成 k-次数。", "infinity_pushforward_degree"], ["代数闭域", "有限剩余域扩张的次数为一，去掉阶数和的权重。", "algebraicallyClosed_infinity_point_degree_one"]], "file": "RationalInfinityResidue.lean", "decl": "rational_infinity_residue_constants_bijective", "related": ["rational_infinity_approximate_constant", "rational_infinity_residue_degree_one", "rational_infinity_inertia_degree_one", "infinity_pushforward_degree", "twoChart_baseField_principal_degree_zero", "algebraicallyClosed_infinity_point_degree_one", "affineDivisorDegree_eq_order_sum"], "deps": ["ratproduct"], "status": "done", "x": 278, "y": 4950, "paper": "proper"});
nodes.push({"id": "curvecenters", "title": "Hartshorne I.6：唯一赋值中心", "statement": "C 为 proper 正规整曲线，A 为包含底域常数的函数域赋值环。实际泛点映射唯一延拓为 Spec A→C，中心处局部环映到 A 是同构；A 非平凡时中心是闭点。", "scope": "实际底域映射、赋值交换方块、唯一延拓及局部环同构全部构造。正规与维数条件推出 stalk 是域或 DVR；同一分式域中的局部赋值环包含必须是同构。不以中心存在或局部环兼容作为输入。", "inputs": ["实际整、局部 Noetherian 的 Scheme C，所有 stalk 整闭且 krullDim C≤1。", "结构态射 C→Spec k 为 proper；A 是实际函数域的赋值子环并包含结构态射给出的常数。"], "steps": [["构造实际底域映射", "从真实泛点与结构态射取出 k→K(C)。", "curveFunctionFieldBaseMap_spec"], ["proper 的唯一延拓", "构造交换方块，再调用已证明的赋值判据。", "proper_functionField_valuation_unique_lift"], ["核对函数域", "中心处 stalk 映射与赋值环包含进入同一个实际函数域。", "valuation_center_stalk_functionField_compat"], ["中心局部环同构", "正规一维 stalk 是域或 DVR，实际局部映射是双射。", "proper_normal_curve_unique_valuation_center_iso"], ["非平凡中心为闭点", "泛点中心会迫使 A 等于整个函数域；余维一点在曲线上闭。", "nontrivial_valuation_center_coheight_one"]], "file": "ValuationCenters.lean", "decl": "proper_normal_curve_unique_valuation_center_iso", "related": ["curveFunctionFieldBaseMap_spec", "local_valuation_fractionRing_bijective", "valuation_generic_lift_over_base", "proper_functionField_valuation_unique_lift", "valuation_center_stalk_functionField_compat", "valuation_center_stalk_bijective", "normal_curve_stalk_isValuation", "nontrivial_valuation_center_coheight_one", "curve_coheight_one_isClosed"], "deps": ["valuative", "dvrfoundation"], "status": "done", "x": 278, "y": 5100, "paper": "proper"});
nodes.push({"id": "curveplaces", "title": "Hartshorne I.6：闭点与赋值环双射", "statement": "proper 正规整曲线的实际余维一闭点，与实际函数域中包含底域的非平凡赋值环一一对应。", "scope": "闭点→赋值环用实际 DVR stalk 在函数域中的像构造；赋值环→闭点由 proper 唯一中心构造。两侧相等与唯一性均已验证。有限／无穷远整闭包素点对这些赋值的分类尚待连接，不能因此宣布全局次数已完成。", "inputs": ["实际 C 正规、整、局部 Noetherian、维数≤1，C→Spec k proper。", "赋值环在实际 K(C) 中，非平凡并包含实际底域常数；无特征限制。"], "steps": [["闭点构造实际赋值环", "取 DVR stalk 的函数域像；均匀化元无正则逆，故赋值非平凡。", "normalCurvePointValuation_ne_top"], ["底域常数", "由实际特化方块证明每个底域常数属于该赋值环。", "normalCurvePointValuation_contains_constants"], ["识别中心子环", "真实 stalk 同构证明中心赋值子环等于原 A。", "normalCurvePointValuation_center_eq"], ["唯一性", "规范闭点延拓与 proper 唯一延拓相同，两点赋值相同则两点相同。", "normalCurvePointValuation_injective"], ["双射", "上述实际构造给出满射与单射。", "proper_normal_curve_points_valuations_bijective"]], "file": "NormalCurveValuations.lean", "decl": "proper_normal_curve_points_valuations_bijective", "related": ["normalCurvePointValuation_ne_top", "normalCurvePointValuation_contains_constants", "normalCurvePointValuation_center_eq", "normalCurvePointValuation_lift", "normalCurvePointValuation_injective", "proper_normal_curve_valuation_has_closed_point"], "deps": ["curvecenters", "dvrfoundation"], "status": "done", "x": 278, "y": 5250, "paper": "proper"});
nodes.push({"id": "curveorders", "title": "实际曲线中心对应保持局部阶数", "statement": "实际函数域的 DVR 赋值环在 proper 正规曲线上有唯一闭点中心，且该对应保持每个非零有理函数的实际局部阶数。", "scope": "使用真实中心 stalk 同构、真实函数域兼容及任意分子分母表示证明阶数相同。没有把阶数保持作为假设。仍需有限／无穷远点分类与全部点的阶数总和传递。", "inputs": ["实际 proper 正规整曲线 C，维数≤1，结构态射到 Spec k。", "A 是包含常数的非平凡实际 DVR 子环；其中心与局部环同构是输出。"], "steps": [["同一分式域的阶数", "实际 DVR 同构和函数域兼容使任意函数的阶数相同。", "dvr_rationalOrder_commonField_ringEquiv"], ["实际 Scheme 中心", "用构造的真实 stalk 同构识别曲线局部阶数。", "normal_curve_valuation_center_order"], ["唯一中心及所有阶数", "同时输出实际闭点、唯一性与全部有理函数的阶数对应。", "proper_normal_curve_valuation_order_correspondence"]], "file": "ValuationOrderTransport.lean", "decl": "proper_normal_curve_valuation_order_correspondence", "related": ["dvr_rationalOrder_commonField_ringEquiv", "normal_curve_valuation_center_order"], "deps": ["curveplaces", "localorder", "rationalorder"], "status": "done", "x": 278, "y": 5400, "paper": "proper"});
find('functionproduct').decl='functionField_principal_order_sum_zero';
find('functionproduct').file='FunctionFieldDegree.lean';
find('functionproduct').related.push('functionField_principal_degree_zero','functionField_principal_degree_baseField_zero','twoChart_baseField_principal_degree_zero','affineDivisorDegree_eq_order_sum');
find('functionproduct').deps.push('infinityresidue');
find('functionproduct').statement='任意特征代数闭底域 k 上，构造的有限处与无穷远实际素点的主除子局部阶数总和为零，无需剩余域权重。';
find('functionproduct').scope='有限可分 L/k(t) 的整闭包、有限性、范数公式、无穷远剩余域及全部 k-权重一均已证明。要求所选参数可分。Hartshorne I.6 的实际曲线点／赋值环双射另已完成；有限／无穷远素点对这些赋值的完整分类及求和传递尚待接通。';
find('functionproduct').inputs[0]='k 为任意特征代数闭域，实际 L/k(t) 有限可分。';
find('functionproduct').steps.push(['统一实际底域','有限处和无穷远次数均为真实 k-剩余域加权次数。','functionField_principal_degree_baseField_zero'],['直接阶数总和','代数闭域的全部实际剩余域次数为一，得到不带权重的阶数和零。','functionField_principal_order_sum_zero']);
for (const id of ['projection','intersection']) find(id).deps.push('curveorders');
find('projection').scope='实际曲线点／赋值环双射、局部阶数保持、无穷远剩余域及构造函数域主除子阶数和零已完成。还需有限／无穷远素点对这些赋值的分类与求和传递、次数的移动／表示无关、全局拉回次数、正规化及点像零次数。完整投影公式仍未通过。';
find('projection').inputs[2]='尚缺：有限／无穷远素点分类及求和传递、次数的移动／表示无关、全局拉回次数、正规化和点像零次数。';
find('projection').steps.splice(3,0,['Hartshorne I.6：已验证','实际曲线闭点与函数域赋值环双射，并保持每个有理函数的局部阶数。','proper_normal_curve_valuation_order_correspondence']);
find('projection').steps[find('projection').steps.length-1]=['全局几何：待完成','将有限／无穷远素点分类及求和接到实际曲线，证明次数与移动无关及拉回次数，再处理正规化和点像。'];
find('projection').precise.zh.gap=find('projection').scope;
find('projection').precise.en.gap='Hartshorne I.6 actual curve-point/valuation bijection, local-order preservation, infinity residue fields and the constructed function-field order sum are proved. Finite/infinity prime classification and sum transport, move/presentation-independent degree, global pullback degree, normalization and point-image zero remain open. The full projection formula is not proved.';
find('intersection').scope='实际 Cartier 限制及有效性阶数正性、实有效分解、Hartshorne I.6 的闭点／赋值环双射及局部阶数保持均已证明。仍须把构造的有限／无穷远素点完整分类并传递主除子总和，接通移动／表示无关、实线性与几何 f-ample 正性。';
find('intersection').inputs[1]='已证明实际曲线点／赋值环双射及阶数保持；尚待有限／无穷远素点完整分类与求和传递，以证明次数的移动和表示无关。';

// Exhaustive actual curve places and principal Cartier degree: formal-21
nodes.push({"id": "dedekindplaces", "title": "Dedekind 图表素点与实际赋值环", "statement": "若非平凡赋值环 A 包含 Dedekind 图表 R，且分式域为 K，则存在唯一高度一素点 p，使 A 等于 p 的实际 adic 赋值子环。", "scope": "从 A 的极大理想收缩构造真实非零素理想。若收缩为零，所有非零分母可逆会迫使 A=K；随后构造实际局部化包含并证明相等。未假定图表中心或素点分类。", "inputs": ["R 为实际 Dedekind 整环，K 为其实际分式域。", "A⊂K 是非平凡赋值子环，并包含 R 的实际像。"], "steps": [["分母逆元", "图表元素的分母若在 A 中为单位，分式仍属于 A。", "valuation_fraction_mem_of_unit_denominator"], ["非零中心", "零收缩会使所有分式正则，导致赋值平凡。", "valuation_chart_center_nonzero"], ["唯一素点", "从真实收缩素理想得到局部化，并核对 adic 子环。", "dedekind_chart_valuation_unique_prime"]], "file": "DedekindValuationPlaces.lean", "decl": "dedekind_chart_valuation_unique_prime", "related": ["valuation_fraction_mem_of_unit_denominator", "valuation_chart_center_nonzero"], "deps": ["dvrfoundation"], "status": "done", "x": 278, "y": 5600, "paper": "proper"});
nodes.push({"id": "chartcover", "title": "全部赋值的有限／无穷远图表覆盖", "statement": "包含底域 k 的函数域赋值环，必包含 k[t] 在 L 中的整闭包，或包含实际无穷远 DVR 在 L 中的整闭包。", "scope": "按参数 t 是否在赋值环中分情况。有限情形使用多项式赋值；极点情形使用分子分母次数比较。赋值环整闭性随后给出实际整闭包包含。没有覆盖假设。", "inputs": ["k 任意域，实际扩张 k(t)→L 与底域结构相容。", "A 是 L 的赋值子环，包含所有底域常数。"], "steps": [["常数赋值", "非零常数及其逆都正则，所以其赋值为一。", "valuation_constants_trivial"], ["整性", "在赋值环内的环上的整元素仍在赋值环内。", "integral_element_mem_valuation"], ["参数极点", "由分子分母次数证明无穷远 DVR 包含。", "rational_infinity_ring_mem_of_parameter_pole"], ["覆盖", "有限图表与无穷远图表覆盖全部实际赋值。", "functionField_valuation_integralClosure_chart_cover"]], "file": "ValuationChartCover.lean", "decl": "functionField_valuation_integralClosure_chart_cover", "related": ["valuation_constants_trivial", "integral_element_mem_valuation", "rational_infinity_ring_mem_of_parameter_pole"], "deps": ["ratproduct"], "status": "done", "x": 278, "y": 5750, "paper": "proper"});
nodes.push({"id": "chartclass", "title": "有限与无穷远素点：完整且互斥", "statement": "有限可分 L/k(t) 中，每个包含底域的非平凡赋值环唯一来自一个有限整闭包素点或一个无穷远整闭包素点。", "scope": "有限处的 t 正则；无穷远处的 1/t 位于收缩极大理想，故 t 有极点。这证明两类不重叠；再结合图表覆盖与唯一素点定理，得到所有赋值的完整分类。", "inputs": ["实际 L/k(t) 为有限可分扩张；任意特征。", "赋值子环非平凡并包含实际底域 k。"], "steps": [["有限处", "参数 t 属于每个有限素点的赋值环。", "finite_place_parameter_regular"], ["无穷远处", "收缩极大理想使 t 有极点。", "infinity_place_parameter_pole"], ["不重叠", "两个图表的素点给出不同赋值环。", "twoChartValuation_injective"], ["完整唯一分类", "图表覆盖加唯一中心给出恰好一个素点。", "functionField_valuation_unique_twoChart_place"]], "file": "FunctionFieldValuationPlaces.lean", "decl": "functionField_valuation_unique_twoChart_place", "related": ["finite_place_parameter_regular", "infinity_place_parameter_pole", "twoChartValuation_injective", "twoChartValuation_ne_top", "twoChartValuation_contains_constants"], "deps": ["chartcover", "dedekindplaces"], "status": "done", "x": 278, "y": 5900, "paper": "proper"});
nodes.push({"id": "adicorders", "title": "adic 阶数与实际 DVR 阶数一致", "statement": "Dedekind 图表素点的归一化 adic 阶数，等于其实际赋值环中分子阶数减分母阶数。", "scope": "由真实均匀化元和理想重数核对归一化，先证明正则方程的阶数一致，再处理任意非零有理函数及极点。只证明赋值子环相同并不足够；归一化也已核对。", "inputs": ["实际 Dedekind 图表及其分式域，高度一素点 p。", "a 为实际函数域的非零有理函数。"], "steps": [["正则方程", "主理想重数等于 DVR 加性阶数。", "dvr_heightOneOrder_regular"], ["包括极点", "任意分式的阶数为分子减分母。", "dvr_heightOneOrder_eq_rationalOrder"], ["图表素点", "均匀化元值 exp(−1) 固定归一化。", "dedekind_prime_order_eq_valuationRing_order"]], "file": "DvrAdicOrders.lean", "decl": "dedekind_prime_order_eq_valuationRing_order", "related": ["dvr_heightOneOrder_regular", "dvr_heightOneOrder_eq_rationalOrder"], "deps": ["localorder", "rationalorder"], "status": "done", "x": 278, "y": 6050, "paper": "proper"});
nodes.push({"id": "curvechartplaces", "title": "实际曲线闭点与两图表素点双射", "statement": "在给定相容有限可分参数下，完整正规曲线的每个实际余维一闭点，恰好对应有限或无穷远整闭包的一个素点。", "scope": "由 Hartshorne I.6 的唯一中心构造实际曲线点，完整分类保证所有点都出现，互斥分类保证不重复。没有输入点清单或点双射。参数存在性仍单独开放。", "inputs": ["C 为实际 proper 正规整、局部 Noetherian 曲线，维数≤1。", "给定与结构态射的 k→K(C) 相容的有限可分参数 k(t)→K(C)。参数存在性尚待从实际曲线构造。"], "steps": [["真实中心", "每个图表素点的赋值环在 C 上有实际闭点中心。", "curve_twoChart_center_exists"], ["赋值一致", "中心点的实际 stalk 赋值就是图表赋值。", "curveTwoChartCenter_valuation"], ["全部点恰一次", "完整且互斥的赋值分类与中心唯一性给出双射。", "proper_normal_curve_twoChart_centers_bijective"]], "file": "CurveChartPlaces.lean", "decl": "proper_normal_curve_twoChart_centers_bijective", "related": ["curve_twoChart_center_exists", "curveTwoChartCenter_valuation"], "deps": ["chartclass", "curveplaces"], "status": "done", "x": 278, "y": 6200, "paper": "proper"});
nodes.push({"id": "curveprincipal", "title": "实际完整曲线：主除子次数零", "statement": "任意特征代数闭域上，在给定相容有限可分参数下，实际 proper 正规曲线的主除子系数为各闭点的真实 ordₚ(a)，支撑有限，且总次数为零。", "scope": "沿已构造的完整点双射搬运两个整闭包图表的实际主除子；逐点证明系数等于真实曲线 stalk 阶数，再搬运范数乘积公式。没有把主除子次数零当成输入。仍须构造参数，完整拉回次数公式尚未完成。", "inputs": ["C 为实际 proper 正规整、局部 Noetherian 曲线，维数≤1。", "给定与结构态射的 k→K(C) 相容的有限可分参数 k(t)→K(C)。参数存在性尚待从实际曲线构造。", "底域 k 为代数闭域；任意特征。"], "steps": [["真实局部阶数", "图表素点阶数等于实际曲线中心的阶数。", "dedekind_prime_actual_curve_order"], ["每个闭点系数", "构造有限支撑除子，并逐点核对 ordₚ(a)。", "curvePrincipalDivisor_coefficient"], ["总次数零", "双射保持求和，由函数域乘积公式得到零。", "proper_normal_curve_principal_degree_zero"]], "file": "CurvePrincipalDegree.lean", "decl": "proper_normal_curve_principal_degree_zero", "related": ["dedekind_prime_actual_curve_order", "twoChartPrincipalDivisor_actual_order", "curvePrincipalDivisor_coefficient"], "deps": ["curvechartplaces", "adicorders", "curveorders", "functionproduct"], "status": "done", "x": 278, "y": 6350, "paper": "proper"});
nodes.push({"id": "cartierprincipal", "title": "Cartier 次数对主除子移动不变", "statement": "实际 proper 正规曲线上，把 Cartier 各局部方程统一乘以非零有理函数 a，不改变其局部阶数总和。", "scope": "逐点证明新除子等于原除子加实际 div(a)，再使用刚证明的主除子次数零。该移动次数缺口已补上；参数存在性、环境曲线正规化、实交数与相对 ample 正性仍须继续接入。", "inputs": ["C 为实际 proper 正规整、局部 Noetherian 曲线，维数≤1。", "给定与结构态射的 k→K(C) 相容的有限可分参数 k(t)→K(C)。参数存在性尚待从实际曲线构造。", "k 为任意特征代数闭域；Cartier 数据为实际仿射局部方程及单位转换。"], "steps": [["所有实际 Scheme 点", "把闭点阶数除子接到整个曲线，并令其他点系数为零。", "curvePrincipalDivisor_allPoints_coefficient"], ["实际除子等式", "方程乘以 a，使各局部阶数增加 ordₚ(a)。", "cartierOrderDivisor_rationalTwist"], ["次数不变", "div(a) 次数零，故移动前后次数相同。", "cartierTotalOrder_rationalTwist"]], "file": "CartierPrincipalDegree.lean", "decl": "cartierTotalOrder_rationalTwist", "related": ["curvePrincipalDivisor_allPoints_coefficient", "cartierOrderDivisor_rationalTwist"], "deps": ["curveprincipal", "cartiercurve"], "status": "done", "x": 278, "y": 6500, "paper": "proper"});

find('projection').deps.push('cartierprincipal');
find('intersection').deps.push('cartierprincipal');
find('curveplaces').scope='实际曲线点／赋值环双射已证明；有限／无穷远素点的完整互斥分类、真实局部阶数及主除子总和现在也已在相容有限可分参数下接通。参数存在性尚待从实际曲线构造。';
find('curveorders').scope='真实 stalk 同构、函数域兼容与分子分母计算证明所有局部阶数保持；现已接到全部有限／无穷远素点，并在相容有限可分参数下搬运主除子次数零。';
find('functionproduct').scope='实际整闭包、范数公式、无穷远剩余域与全部 k-权重一已证明。所有有限／无穷远赋值现已完整且互斥地分类，已将阶数总和接到给定完整正规曲线。仍显式要求相容有限可分参数，不能隐去其存在性。';
find('projection').scope='已补齐全部有限／无穷远素点分类、实际闭点求和、归一化阶数一致及 Cartier 主除子移动次数不变；均在显式给定的相容有限可分参数下。尚缺参数存在性、全局拉回次数公式、曲线正规化及像为点的零次数。完整投影公式仍未完成。';
find('projection').inputs[2]='尚缺：从实际曲线构造相容有限可分参数；全局拉回次数、曲线正规化和点像零次数。';
find('projection').steps.splice(find('projection').steps.length-1,0,['完整曲线主除子：已验证','每个实际闭点系数为真实局部阶数，总次数零；参数假设显式列出。','proper_normal_curve_principal_degree_zero'],['主除子移动：已验证','Cartier 局部方程乘以全局有理函数不改变次数。','cartierTotalOrder_rationalTwist']);
find('projection').steps[find('projection').steps.length-1]=['剩余几何：待完成','构造相容可分参数，接通全局拉回次数、正规化与点像零次数。'];
find('projection').precise.zh.gap=find('projection').scope;
find('projection').precise.en.gap='Exhaustive disjoint finite/infinity places, actual closed-point order sums, normalized DVR orders and Cartier principal-move invariance are now proved with an explicit compatible finite separable parameter. Parameter existence, global pullback degree, curve normalization and point-image zero remain open. The full projection formula is not proved.';
find('intersection').scope='实际 Cartier 限制、有效性正性、实有效分解、全部闭点／赋值对应、实际主除子次数零和主除子移动次数不变均已证明，后两项使用显式相容有限可分参数。还需从曲线构造参数，接通正规化、实交数的完整表示无关和几何 f-ample 正性。';
find('intersection').inputs[1]='主除子移动次数已证明不变；仍须构造相容可分参数，完成正规化、实交数接口与相对 ample 的几何正性。';

// Actual curve geometry eliminates parameter inputs: formal-22
nodes.push({"id": "separatingparameter", "title": "可分参数：任意特征", "statement": "完美底域 k 上本质有限型、超越次数一的函数域 L，存在相容的 k(t)→L，使 L/k(t) 有限可分。", "scope": "使用实际可分超越基，证明其仅有一个元素，再构造有理函数域的实际嵌入。仅常数域 k 要求 perfect，未要求 k(t) perfect。", "inputs": ["k 为完美域，L 为 k 上的实际本质有限型域。", "trdegₖ L=1。实际曲线的这两个条件由相邻几何节点证明。"], "steps": [["单元素超越基", "由超越次数一取出一个实际超越元。", "exists_finite_separable_transcendental_parameter"], ["实际嵌入", "构造相容的 k(t)→L 并传递有限性、可分性。", "exists_compatible_finite_separable_ratFunc_embedding"]], "file": "SeparatingParameter.lean", "decl": "exists_compatible_finite_separable_ratFunc_embedding", "related": ["exists_finite_separable_transcendental_parameter"], "deps": [], "status": "done", "x": 278, "y": 6650, "paper": "proper"});
nodes.push({"id": "affinecurvefield", "title": "仿射曲线函数域：有限型与超越次数", "statement": "有限型 k-整环 R 维数≤1 且不是域时，其实际分式域 L 满足本质有限型及 trdegₖ L=1。", "scope": "从 Noether 正规化构造多项式子环。用 lying over 与极大理想收缩证明变量数≤1，非域排除零变量；再将超越次数传递到实际分式域。", "inputs": ["R 为有限型 k-整环，Krull 维数≤1，且非域。", "L 为 R 的实际分式域，底域结构相容。"], "steps": [["整子环维数", "lying over 和极大收缩保持维数上界。", "integral_subring_krullDimLE_one"], ["恰好一维", "Noether 正规化的变量数恰好为一。", "affine_curve_ring_trdeg_one"], ["实际分式域", "分式局部化给出本质有限型及超越次数一。", "affine_curve_fractionField_finiteType_trdeg_one"]], "file": "AffineCurveFunctionField.lean", "decl": "affine_curve_fractionField_finiteType_trdeg_one", "related": ["integral_subring_krullDimLE_one", "affine_curve_ring_trdeg_one"], "deps": [], "status": "done", "x": 278, "y": 6800, "paper": "proper"});
nodes.push({"id": "curveparameter", "title": "实际曲线：自动构造可分参数", "statement": "实际有限型一维整曲线 C 的函数域，自动存在相容有限可分参数 k(t)→K(C)；无需再提供函数域有限型或超越次数。", "scope": "从维数选取实际余维一点及其仿射邻域，证明该图表一维、非域、有限型；核对常数交换方块和分式域，再应用可分参数构造。", "inputs": ["C 为实际一维整 Scheme，b:C→Spec k 为有限型态射。", "k 为任意特征代数闭域；常数嵌入是实际结构态射在泛点给出的映射。"], "steps": [["实际图表", "维数上界及非域性来自实际余维一点。", "curve_affine_chart_not_field"], ["泛点常数", "图表常数与实际函数域常数一致。", "curve_affine_constants_compatible"], ["函数域性质", "由实际 Scheme 的有限型和维数推出域性质。", "curve_functionField_properties_of_closed_point"], ["无需参数输入", "由实际曲线自动构造相容有限可分参数。", "finiteType_curve_exists_separating_parameter"]], "file": "CurveFunctionField.lean", "decl": "finiteType_curve_exists_separating_parameter", "related": ["curve_affine_chart_dimension", "curve_affine_chart_not_field", "curve_affine_constants_compatible", "curve_functionField_properties_of_closed_point", "curve_exists_coheight_one"], "deps": ["affinecurvefield", "separatingparameter"], "status": "done", "x": 278, "y": 6950, "paper": "proper"});
nodes.push({"id": "curveproductcomplete", "title": "完整正规曲线乘积公式：参数已消去", "statement": "任意特征代数闭域上的实际完整正规整曲线，每个非零有理函数的主除子支撑有限、系数为真实 ordₚ(a)，且 Σₚ ordₚ(a)=0。", "scope": "实际曲线自动构造可分参数，再使用已验证的 Hartshorne I.6 唯一中心、完整互斥赋值分类和局部阶数传递。主除子次数零、参数存在性、点清单均不是输入。", "inputs": ["C 为实际一维整 Scheme，b:C→Spec k 为有限型态射。", "k 为任意特征代数闭域；常数嵌入是实际结构态射在泛点给出的映射。", "C proper、局部 Noetherian，所有实际 stalk 整闭；a∈K(C)ˣ。"], "steps": [["由几何到乘积公式", "自动构造参数后，搬运实际曲线主除子的局部阶数及次数零。", "complete_normal_curve_principal_product_formula"]], "file": "CurveProductFormula.lean", "decl": "complete_normal_curve_principal_product_formula", "related": [], "deps": ["curveparameter", "curveprincipal"], "status": "done", "x": 278, "y": 7100, "paper": "proper"});
nodes.push({"id": "cartierdegreecomplete", "title": "完整曲线 Cartier 移动：无参数输入", "statement": "实际完整正规曲线上，Cartier 局部方程统一乘以 a∈K(C)ˣ 不改变次数；无需额外可分参数或紧性输入。", "scope": "由 proper 推出实际紧性，由有限型一维曲线构造参数，再使用逐点主除子等式与次数零。环境曲线正规化、完整拉回次数和几何 ample 正性仍须继续完成。", "inputs": ["C 为实际一维整 Scheme，b:C→Spec k 为有限型态射。", "k 为任意特征代数闭域；常数嵌入是实际结构态射在泛点给出的映射。", "C proper、局部 Noetherian、stalk 整闭；实际 CartierAtlas 局部方程及单位转换。"], "steps": [["移动次数不变", "自动构造参数、导出紧性并证明实际 Cartier 次数不变。", "complete_normal_curve_cartier_degree_invariant"]], "file": "CartierDegreeInvariance.lean", "decl": "complete_normal_curve_cartier_degree_invariant", "related": [], "deps": ["curveparameter", "cartierprincipal", "curveproductcomplete"], "status": "done", "x": 278, "y": 7250, "paper": "proper"});

find('projection').deps.push('cartierdegreecomplete');
find('intersection').deps.push('cartierdegreecomplete');
find('projection').scope='实际完整正规曲线的可分参数存在性已由 Scheme 的有限型及一维条件证明；主除子次数零和 Cartier 主除子移动次数不变不再要求参数输入。尚缺全局拉回次数、曲线正规化及像为点的零次数。完整投影公式仍未完成。';
find('projection').inputs[2]='尚缺：全局拉回次数公式、环境曲线正规化和像为点的零次数。';
find('projection').steps[find('projection').steps.length-1]=['剩余几何：待完成','接通全局拉回次数、曲线正规化与点像零次数；实际曲线可分参数已构造。'];
find('projection').precise.zh.gap=find('projection').scope;
find('projection').precise.en.gap='The separating parameter is constructed from actual finite-type one-dimensional Scheme geometry. Principal degree zero and Cartier principal-move invariance no longer require a parameter input. Global pullback degree, curve normalization and point-image zero remain open; the full projection formula is unfinished.';
find('intersection').scope='实际完整正规曲线可分参数、主除子次数零及 Cartier 移动次数不变现已全部从 Scheme 几何推出。尚需环境曲线正规化、实交数的表示无关及几何 f-ample 正性；完整 negativity lemma 仍未完成。';
find('intersection').inputs[1]='实际曲线参数与主除子移动次数已完成。剩余：环境曲线正规化、实交数表示无关与几何 f-ample 正性。';

for (const id of ['curvechartplaces','curveprincipal','cartierprincipal']) {
  const n=find(id);
  n.scope += ' 实际曲线的参数存在性现已由 curveparameter 证明；无参数输入的最终乘积公式与移动次数不变见新节点。';
  n.inputs=n.inputs.map(t=>t.replace('参数存在性尚待从实际曲线构造。','参数存在性已在实际曲线参数节点证明。'));
}

find('curvechartplaces').scope='该辅助定理使用显式参数，构造完整互斥素点与实际曲线闭点的双射。参数存在性已从实际一维有限型 Scheme 证明，无参数输入的最终乘积公式见 curveproductcomplete。';
find('curveprincipal').scope='该辅助定理在相容参数下逐点识别真实阶数，并证明主除子次数零。参数存在性现已从实际曲线构造；无需参数输入的完整定理见 curveproductcomplete。全局拉回次数仍开放。';
find('cartierprincipal').scope='逐点实际主除子等式与次数零证明移动次数不变。参数存在性已完成；无需参数及紧性输入的最终实际曲线定理见 cartierdegreecomplete。';
find('curveplaces').scope='Hartshorne I.6 的实际唯一中心与闭点／赋值环双射已完成；全部图表赋值、局部阶数和总和已接通。相容可分参数也已由实际曲线的有限型和维数条件构造。';
find('functionproduct').scope='实际整闭包、范数、无穷远剩余域及权重已完成，完整赋值分类已搬运到曲线。相容可分参数现已由实际一维有限型 Scheme 构造；最终完整曲线乘积公式没有参数输入。';

// Actual proper-curve Cartier pullback degrees: formal-23
nodes.push({"id": "affineorders", "title": "仿射素点与实际 stalk 阶数", "statement": "正规整曲线的实际仿射坐标环是 Dedekind 环，素点的归一化赋值阶数等于对应实际曲线点的 stalk 阶数。", "scope": "用实际局部化的唯一性构造共同函数域中的局部环同构；不是另加阶数相容性输入。", "inputs": ["实际局部 Noetherian 整 Scheme，所有 stalk 整闭，维数≤1。", "实际非空仿射开 U。"], "steps": [["仿射素点与实际 stalk 阶数", "用实际局部化的唯一性构造共同函数域中的局部环同构；不是另加阶数相容性输入。", "normal_curve_affine_prime_order"]], "file": "AffineCurveOrders.lean", "decl": "normal_curve_affine_prime_order", "related": ["normal_curve_affine_dedekind", "curve_affine_prime_coheight"], "deps": ["normalsections", "adicorders"], "status": "done", "x": 278, "y": 7550, "paper": "proper"});
nodes.push({"id": "finiteorders", "title": "有限曲线态射的带权局部次数", "statement": "对实际有限 dominant 正规曲线态射，Σₓ ordₓ(f*a)[κ(x):κ(y)]=[K(X):K(Y)]ordᵧ(a)。", "scope": "实际 section-map 与泛点映射给出相容域塔。有限性、无挠性及平坦性均从实际几何导出；不要求可分。", "inputs": ["实际有限 dominant 态射 f:X→Y；X、Y 正规整、局部 Noetherian，维数≤1。", "y 的实际仿射图表及非零有理函数 a。"], "steps": [["有限曲线态射的带权局部次数", "实际 section-map 与泛点映射给出相容域塔。有限性、无挠性及平坦性均从实际几何导出；不要求可分。", "finite_normal_curve_fiber_order_degree"]], "file": "FiniteCurveOrders.lean", "decl": "finite_normal_curve_fiber_order_degree", "related": ["finite_curve_chart_generic_tower", "dominant_curve_chart_torsionFree"], "deps": ["affineorders", "localprojection", "cartierpullback"], "status": "done", "x": 278, "y": 7700, "paper": "proper"});
nodes.push({"id": "fiberprimes", "title": "实际纤维点与图表素理想", "statement": "有限态射的图表中，位于 p 之上的坐标环素理想与 {x∈X | f(x)=y} 实际双射。", "scope": "两个方向使用实际 fromSpec 与 primeIdealOf；section-map 交换方块证明 lying over。纤维点清单不是输入。", "inputs": ["实际 affine 态射及目标仿射开 U。", "p 为 Γ(Y,U) 的实际素理想。"], "steps": [["实际纤维点与图表素理想", "两个方向使用实际 fromSpec 与 primeIdealOf；section-map 交换方块证明 lying over。纤维点清单不是输入。", "curve_fiber_primes_actual_bijective"]], "file": "CurveFiberPrimes.lean", "decl": "curve_fiber_primes_actual_bijective", "related": ["curve_chart_point_mem", "curve_primeOver_maps_to_fiber", "curve_fiber_point_prime_liesOver"], "deps": ["cartierpullback"], "status": "done", "x": 278, "y": 7850, "paper": "proper"});
nodes.push({"id": "closedresidue", "title": "代数闭底域：剩余次数等于一", "statement": "任意特征代数闭域上的实际有限 dominant 正规曲线态射，每个闭点纤维素理想满足 [κ(x):κ(y)]=1。", "scope": "从实际结构态射构造常数环作用及相容域塔，用有限型与 Zariski 引理计算剩余次数；未假定可分。", "inputs": ["k 为任意特征代数闭域；Y→Spec k 为有限型。", "实际有限 dominant 正规曲线态射，实际闭点纤维。"], "steps": [["代数闭底域：剩余次数等于一", "从实际结构态射构造常数环作用及相容域塔，用有限型与 Zariski 引理计算剩余次数；未假定可分。", "finite_normal_curve_relative_residueDegree_one"]], "file": "CurveClosedResidue.lean", "decl": "finite_normal_curve_relative_residueDegree_one", "related": ["curve_chart_base_scalar_tower", "curve_chart_base_finiteType"], "deps": ["affineorders", "finitecurvepoints"], "status": "done", "x": 278, "y": 8000, "paper": "proper"});
nodes.push({"id": "fiberorders", "title": "实际纤维：按重数求和", "statement": "对实际有限 dominant 正规曲线态射，Σ_{f(x)=y} ordₓ(f*a)=[K(X):K(Y)]ordᵧ(a)。", "scope": "求和覆盖所有实际纤维点，其余维一性质及剩余次数一均已证明。包含纯不可分态射。", "inputs": ["k 为任意特征代数闭域。", "实际有限 dominant 正规曲线态射、闭点 y 与非零有理函数 a。"], "steps": [["实际纤维：按重数求和", "求和覆盖所有实际纤维点，其余维一性质及剩余次数一均已证明。包含纯不可分态射。", "finite_normal_curve_actual_fiber_order_degree"]], "file": "CurveFiberDegree.lean", "decl": "finite_normal_curve_actual_fiber_order_degree", "related": ["finite_normal_curve_unweighted_order_degree"], "deps": ["finiteorders", "fiberprimes", "closedresidue"], "status": "done", "x": 278, "y": 8150, "paper": "proper"});
nodes.push({"id": "finitecurvepoints", "title": "有限曲线态射保持闭点", "statement": "实际有限 dominant 正规曲线态射将余维一点映到余维一点；非空仿射开的逆像也非空。", "scope": "通过实际图表整扩张的素理想收缩证明闭点性质。图表点的识别和 lying over 均由实际 Scheme 给出。", "inputs": ["实际有限 dominant 正规整曲线态射，维数≤1。", "实际余维一点 x。"], "steps": [["有限曲线态射保持闭点", "通过实际图表整扩张的素理想收缩证明闭点性质。图表点的识别和 lying over 均由实际 Scheme 给出。", "finite_normal_curve_maps_coheight_one"]], "file": "FiniteCurvePoints.lean", "decl": "finite_normal_curve_maps_coheight_one", "related": ["curve_affine_point_heightOne", "finite_dominant_curve_preimage_nonempty"], "deps": ["affineorders", "fiberprimes"], "status": "done", "x": 278, "y": 8300, "paper": "proper"});
nodes.push({"id": "cartierfiber", "title": "Cartier 拉回的实际纤维系数", "statement": "构造实际 Cartier 拉回 B=f*D，并证明每个闭点 y 有 Σ_{f(x)=y} coeffₓ(B)=[K(X):K(Y)]coeffᵧ(D)。", "scope": "输出包含实际拉回图表和局部方程，不只是存在某个次数相等的除子；逐点 Cartier 系数由真实 stalk 阶数计算。", "inputs": ["任意特征代数闭域上的实际有限 dominant 正规曲线态射。", "实际 Cartier 局部方程与单位转换。"], "steps": [["Cartier 拉回的实际纤维系数", "输出包含实际拉回图表和局部方程，不只是存在某个次数相等的除子；逐点 Cartier 系数由真实 stalk 阶数计算。", "finite_normal_curve_cartier_fiber_orders"]], "file": "CurveCartierFiber.lean", "decl": "finite_normal_curve_cartier_fiber_orders", "related": [], "deps": ["fiberorders", "finitecurvepoints", "cartierpullback"], "status": "done", "x": 278, "y": 8450, "paper": "proper"});
nodes.push({"id": "cartierglobal", "title": "Cartier 全局次数：实际有限拉回", "statement": "在实际紧正规整曲线上，构造 B=f*D 并证明 deg(B)=[K(X):K(Y)]deg(D)。", "scope": "先证明实际 Cartier 推拉系数，再利用有限支撑求和。全局投影公式及局部系数相容性均不是假设。", "inputs": ["实际有限 dominant 正规曲线态射，维数≤1，实际底域代数闭。", "源与目标紧；D 为实际 CartierAtlas。"], "steps": [["Cartier 全局次数：实际有限拉回", "先证明实际 Cartier 推拉系数，再利用有限支撑求和。全局投影公式及局部系数相容性均不是假设。", "finite_normal_curve_cartier_pullback_degree"]], "file": "CurveCartierDegree.lean", "decl": "finite_normal_curve_cartier_pullback_degree", "related": ["finsupp_mapDomain_actual_fiber", "finite_normal_curve_cartier_push_pull"], "deps": ["cartierfiber", "finitecurvepoints"], "status": "done", "x": 278, "y": 8600, "paper": "proper"});
nodes.push({"id": "propercurvefinite", "title": "proper 曲线态射自动有限", "statement": "一维 Noetherian 整曲线间的实际 proper dominant 态射是有限态射。", "scope": "非泛点纤维为真闭子集；泛点纤维不能含闭点。实际有限纤维给出 quasi-finite，再接入 Zariski 主定理。此步不要求正规或可分。", "inputs": ["X、Y 为实际一维整 Scheme，X Noetherian。", "f:X→Y 为实际 proper dominant 态射。"], "steps": [["proper 曲线态射自动有限", "非泛点纤维为真闭子集；泛点纤维不能含闭点。实际有限纤维给出 quasi-finite，再接入 Zariski 主定理。此步不要求正规或可分。", "proper_dominant_integral_curve_isFinite"]], "file": "ProperCurveFinite.lean", "decl": "proper_dominant_integral_curve_isFinite", "related": ["curve_coheight_zero_generic", "curve_nonGeneric_coheight_one", "curve_genericPoint_not_closed", "proper_dominant_curve_fibers_finite"], "deps": ["zmtfinite", "curvecenters"], "status": "done", "x": 278, "y": 8750, "paper": "proper"});
nodes.push({"id": "propercurveglobal", "title": "完整正规曲线：Cartier 拉回次数", "statement": "任意特征代数闭域上，完整正规整曲线间 proper dominant 态射满足 deg(f*D)=[K(X):K(Y)]deg(D)。", "scope": "有限性与紧性来自实际 proper 曲线几何；输出真实拉回方程。无需可分性、纤维枚举、局部交数相容性或次数公式输入。环境曲线正规化及像为点的零次数仍待完成。", "inputs": ["k 为任意特征代数闭域；X、Y 为一维整、局部 Noetherian、stalk 整闭的实际 Scheme。", "Y→Spec k proper；f:X→Y proper dominant；D 为实际 CartierAtlas。"], "steps": [["完整正规曲线：Cartier 拉回次数", "有限性与紧性来自实际 proper 曲线几何；输出真实拉回方程。无需可分性、纤维枚举、局部交数相容性或次数公式输入。环境曲线正规化及像为点的零次数仍待完成。", "complete_normal_curve_cartier_pullback_degree"]], "file": "ProperCurveCartierDegree.lean", "decl": "complete_normal_curve_cartier_pullback_degree", "related": ["complete_normal_curve_finite_cartier_pullback_degree"], "deps": ["cartierglobal", "propercurvefinite"], "status": "done", "x": 278, "y": 8900, "paper": "proper"});

find('projection').deps.push('propercurveglobal');
find('projection').scope='实际完整正规曲线间 proper dominant 态射的 Cartier 拉回次数公式现已证明，包括不可分次数；实际纤维、局部方程及有限性全部从几何导出。尚缺环境曲线正规化、像为点的零次数和实交数的完整接入。完整环境投影公式仍未完成。';
find('projection').inputs[2]='尚缺：环境曲线正规化、像为点的零次数及实交数接入。完整正规曲线的全局 Cartier 拉回次数已完成。';
find('projection').steps[find('projection').steps.length-1]=['完整曲线次数：已验证','proper dominant 完整正规曲线的实际 Cartier 拉回次数已完成；继续环境正规化及点像零次数。','complete_normal_curve_cartier_pullback_degree'];
find('projection').precise.zh.gap=find('projection').scope;
find('projection').precise.en.gap='Global Cartier pullback degree for actual proper dominant complete normal curves is proved, including inseparable degree. Actual fibers, local equations and finiteness are derived. Ambient normalization, point-image zero and full real-intersection integration remain open; the ambient projection formula is unfinished.';
for(const id of ['curveprincipal','cartierdegreecomplete']) find(id).scope+=' 实际 proper 曲线的全局 Cartier 拉回次数现已在 propercurveglobal 完成；环境正规化及点像情形另行继续。';

find('propercurveglobal').scope+=' 次数包含不可分部分。';

// Actual choice-independent Cartier curve intersection: formal-24
nodes.push({"id": "pointimagezero", "title": "点像：实际移动限制次数为零", "statement": "若实际态射 f:C→X 将 C 的所有点映到同一点，则构造移动后的 Cartier 限制 B，其每个实际局部方程均为 1，故 deg(B)=0。", "scope": "通过该点附近的实际 Cartier 方程移动，再用真实泛点 stalk 单位构造限制。此构造的次数为零；选择无关性在 actualintersection 接通。", "inputs": ["C、X 是实际整 Scheme；C 局部 Noetherian、紧且各 stalk 整闭。", "实际态射 f；∀x，f(x)=f(ηC)；X 上实际 CartierAtlas A。"], "steps": [["点像：实际移动限制次数为零", "通过该点附近的实际 Cartier 方程移动，再用真实泛点 stalk 单位构造限制。此构造的次数为零；选择无关性在 actualintersection 接通。", "constant_image_moved_cartier_restriction_degree_zero"]], "file": "CurvePointImageDegree.lean", "decl": "constant_image_moved_cartier_restriction_degree_zero", "related": ["cartierTotalOrder_zero_of_equations_one"], "deps": ["cartiercurve"], "status": "done", "x": 278, "y": 9100, "paper": "proper"});
nodes.push({"id": "curvemoveindependent", "title": "实际曲线：不同移动次数相同", "statement": "在完整正规整曲线上，对同一环境 Cartier 除子的任意两次实际移动限制 B₁、B₂，都有 deg(B₂)=deg(B₁)。", "scope": "两条环境移动函数各自未必能拉回；证明其比值在泛点像处是实际单位，将比值拉回后得到曲线主除子，再用主除子次数零。未输入比值或次数相等式。", "inputs": ["k 为任意特征代数闭域；C 为一维、局部 Noetherian、stalk 整闭的整 Scheme，C→Spec k proper。", "实际态射 C→X 及同一 CartierAtlas；两组实际局部方程／stalk 限制数据，不含数值恒等式。"], "steps": [["实际曲线：不同移动次数相同", "两条环境移动函数各自未必能拉回；证明其比值在泛点像处是实际单位，将比值拉回后得到曲线主除子，再用主除子次数零。未输入比值或次数相等式。", "complete_normal_curve_moved_restriction_degree_independent"]], "file": "CurveMoveDegree.lean", "decl": "complete_normal_curve_moved_restriction_degree_independent", "related": ["moved_cartier_restriction_ratio_equations"], "deps": ["cartiercurve", "cartierdegreecomplete"], "status": "done", "x": 278, "y": 9250, "paper": "proper"});
nodes.push({"id": "actualintersection", "title": "真实 Cartier 交数：选择无关与点像零", "statement": "对实际完整正规曲线 C→X，以移动后的 Cartier 限制局部阶数和定义 A·C；任何合法移动及源仿射图表选择给出相同值。若曲线被压缩为点，则 A·C=0。", "scope": "交数由实际 stalk 方程构造，不是给定的线性接口。包含曲线原来位于除子支撑内的情形。尚未声称完成环境曲线正规化或任意实表示的独立性。", "inputs": ["k 为任意特征代数闭域；C proper、一维、整、局部 Noetherian、stalk 整闭。", "X 整；任意实际态射 f:C→X；A 为实际 Cartier 局部方程与单位转换。"], "steps": [["真实 Cartier 交数：选择无关与点像零", "交数由实际 stalk 方程构造，不是给定的线性接口。包含曲线原来位于除子支撑内的情形。尚未声称完成环境曲线正规化或任意实表示的独立性。", "complete_normal_curve_cartier_intersection_wellDefined"]], "file": "CartierCurveIntersection.lean", "decl": "complete_normal_curve_cartier_intersection_wellDefined", "related": ["complete_normal_curve_cartier_intersection_eq_restriction"], "deps": ["pointimagezero", "curvemoveindependent"], "status": "done", "x": 278, "y": 9400, "paper": "proper"});
nodes.push({"id": "effectiveintersection", "title": "真实交数：有效除子的非负与严格正", "statement": "若实际有效 Cartier 除子 A 的支撑不包含曲线 C，则 A·C≥0；若曲线同时与支撑相交，则 A·C>0。", "scope": "使用已定义且选择无关的实际交数。正规局部方程的有效性、全支撑逆像及每点局部阶数均从 stalk 映射导出；非负／正交数不是参数。", "inputs": ["k 为任意特征代数闭域；C 为实际完整正规整曲线；任意实际态射 f:C→X。", "A.Effective 为局部正规方程的有效性定义；f(ηC) 不在支撑中；严格正结论另要求逆像支撑非空。"], "steps": [["真实交数：有效除子的非负与严格正", "使用已定义且选择无关的实际交数。正规局部方程的有效性、全支撑逆像及每点局部阶数均从 stalk 映射导出；非负／正交数不是参数。", "complete_normal_curve_effective_cartier_intersection_signs"]], "file": "EffectiveCurveIntersection.lean", "decl": "complete_normal_curve_effective_cartier_intersection_signs", "related": ["effective_cartier_restriction_with_data"], "deps": ["actualintersection", "cartiercurve"], "status": "done", "x": 278, "y": 9550, "paper": "proper"});
nodes.push({"id": "curveintersectiondegree", "title": "真实 Cartier 交数：完整曲线次数倍", "statement": "完整正规整曲线间的实际 proper dominant 态射 f:C→X 满足 A·C=[K(C):K(X)]deg(A)，这里交数使用已定义且移动选择无关的局部阶数和。", "scope": "识别实际泛点 stalk 限制与函数域拉回的局部方程，再接入已证明的完整曲线次数公式。包含不可分次数；仍须将环境交换图、正规化与实除子完整接入。", "inputs": ["k 为任意特征代数闭域；C、X 一维、整、局部 Noetherian且各 stalk 整闭。", "X→Spec k proper；f:C→X proper dominant；A 为实际 CartierAtlas。"], "steps": [["真实 Cartier 交数：完整曲线次数倍", "识别实际泛点 stalk 限制与函数域拉回的局部方程，再接入已证明的完整曲线次数公式。包含不可分次数；仍须将环境交换图、正规化与实除子完整接入。", "complete_normal_curve_cartier_intersection_degree"]], "file": "CurveIntersectionDegree.lean", "decl": "complete_normal_curve_cartier_intersection_degree", "related": ["generic_stalk_functionField_self", "genericPoint_not_cartier_support", "dominant_moved_restriction_equations"], "deps": ["actualintersection", "propercurveglobal"], "status": "done", "x": 278, "y": 9700, "paper": "proper"});
find('projection').deps.push('actualintersection','curveintersectiondegree');
find('projection').scope="实际完整正规曲线的 Cartier 交数已构造并证明移动／源图表选择无关；点像零交数、有效除子正性与 proper dominant 曲线次数倍均已通过 Lean，包含不可分次数。仍缺环境正规化、环境 Cartier 拉回的完整复合相容性及任意实表示的交数独立性。完整环境投影公式仍未完成。";
find('intersection').deps.push('actualintersection','effectiveintersection');
find('intersection').scope="已经构造真实完整正规曲线上的 Cartier 交数，并证明移动／源图表选择无关、点像零值及有效除子的非负／相交时严格正。f-nef 的数值符号按被压缩完整曲线的定义理解；尚缺环境正规化、任意实表示的线性和几何 f-ample 正性。";
find('projection').inputs[2]='仍缺：环境正规化、环境拉回复合相容性及任意实表示交数独立性。实际 Cartier 曲线的零值与次数倍已完成。';
find('projection').steps.push(['真实交数：已验证','实际 Cartier 交数的移动无关、点像零值与完整曲线次数倍现已完成。','complete_normal_curve_cartier_intersection_degree']);
find('projection').precise.zh.gap=find('projection').scope;
find('projection').precise.en.gap='Actual choice-independent Cartier curve intersection, contracted-curve zero, effective-divisor signs and proper dominant complete-curve degree are proved, including inseparable degree. Ambient normalization, ambient pullback composition and arbitrary real-presentation independence remain open. The full ambient projection formula is unfinished.';
find('intersection').inputs=['已完成：实际 Cartier 交数、移动／源图表选择无关、点像零值、有效除子的非负与相交时严格正。','尚缺：环境曲线正规化与任意实表示的线性／独立性。','C 为被 f 压缩的完整曲线；f-nef 数值符号是定义；几何 f-ample 的正次数仍待接通。'];
find('intersection').steps=[['真实交数与移动无关','从实际局部方程构造交数；合法移动与源图表选择给相同值。','complete_normal_curve_cartier_intersection_wellDefined'],['有效除子正性','不包含曲线时非负，同时相交时严格正；符号由实际阶数导出。','complete_normal_curve_effective_cartier_intersection_signs'],['剩余几何','正规化、实表示独立性与几何 f-ample 正性仍待完成。']];
for(const id of ['cartiercurve','propercurveglobal','cartierdegreecomplete']) find(id).scope+=' 后续 actualintersection 已完成真正的 Cartier 交数定义、移动选择无关与点像零值；effectiveintersection 接通有效除子正性，curveintersectiondegree 接通次数倍。完整环境及实除子投影仍未完成。';

// Actual integer/real Cartier intersection and ambient pullback: formal-25
nodes.push({"id": "ambientmoving", "title": "环境主除子移动：交数不变", "statement": "对任意环境有理函数 a，(A+div(a))·C=A·C，即使 a 本身不能拉回到 C。", "scope": "通过抵消两次环境移动构造同一实际限制；没有把主除子交数零作为假设。", "inputs": ["k 为任意特征代数闭域；C 为 proper、一维、局部 Noetherian、stalk 整闭的整 Scheme。", "实际完整正规整曲线 C→X；实际 CartierAtlas A 及环境函数 a。"], "steps": [["环境主除子移动：交数不变", "通过抵消两次环境移动构造同一实际限制；没有把主除子交数零作为假设。", "complete_normal_curve_ambient_cartier_principal_invariance"]], "file": "AmbientCartierMoving.lean", "decl": "complete_normal_curve_ambient_cartier_principal_invariance", "related": ["movedCartierRestrictionData_rationalTwist"], "deps": ["actualintersection"], "status": "done", "x": 278, "y": 10000, "paper": "proper"});
nodes.push({"id": "zerointersection", "title": "零 Weil 系数：真实交数为零", "statement": "正规环境上，实际 Cartier 除子的所有 Weil 系数为零，则它与实际完整正规曲线的交数为零。", "scope": "从正规性推出完整支撑为空，构造实际有效限制并求局部阶数。支撑为空和零交数均是结论。", "inputs": ["k 为任意特征代数闭域；C 为 proper、一维、局部 Noetherian、stalk 整闭的整 Scheme。", "X 为局部 Noetherian 正规整 Scheme；A 的全部实际 Weil 系数为零。"], "steps": [["零 Weil 系数：真实交数为零", "从正规性推出完整支撑为空，构造实际有效限制并求局部阶数。支撑为空和零交数均是结论。", "complete_normal_curve_zero_cartier_intersection"]], "file": "CartierZeroIntersection.lean", "decl": "complete_normal_curve_zero_cartier_intersection", "related": ["cartier_support_empty_of_coefficients_zero", "cartierTotalOrder_zero_of_support_empty"], "deps": ["effectiveintersection", "cartiersupport"], "status": "done", "x": 278, "y": 10150, "paper": "proper"});
nodes.push({"id": "integerintersection", "title": "真实交数：整数可加性", "statement": "构造实际局部方程乘积 D=ΣnᵢAᵢ，并证明 D·C=Σnᵢ(Aᵢ·C)。", "scope": "构造实际仿射图表和单位转换，再从 DVR 局部阶数导出可加性；线性接口不是参数。", "inputs": ["k 为任意特征代数闭域；C 为 proper、一维、局部 Noetherian、stalk 整闭的整 Scheme。", "有限组真实环境 Cartier atlases；任意整数权重；实际 C→X。"], "steps": [["真实交数：整数可加性", "构造实际仿射图表和单位转换，再从 DVR 局部阶数导出可加性；线性接口不是参数。", "exists_complete_curve_cartier_intersection_integralCombination"]], "file": "CurveCartierCombinations.lean", "decl": "exists_complete_curve_cartier_intersection_integralCombination", "related": ["moved_restriction_equation_on_chart", "integral_combination_moved_local_units"], "deps": ["actualintersection"], "status": "done", "x": 278, "y": 10300, "paper": "proper"});
nodes.push({"id": "realintersectionkernel", "title": "真实实交数：系数相消不改变值", "statement": "同一有限组真实 Cartier 生成元中，代表相同实际 Weil 系数的两个实系数组合具有相同交数。", "scope": "先证明实际整数零关系，再清分母；用有理系数核生成任意实零关系。不要求环境全局支撑有限。", "inputs": ["k 为任意特征代数闭域；C 为 proper、一维、局部 Noetherian、stalk 整闭的整 Scheme。", "正规、局部 Noetherian 整环境；有限实际 Cartier 生成元及两个实权重向量。"], "steps": [["真实实交数：系数相消不改变值", "先证明实际整数零关系，再清分母；用有理系数核生成任意实零关系。不要求环境全局支撑有限。", "complete_normal_curve_real_cartier_intersection_wellDefined"]], "file": "RealCurveIntersection.lean", "decl": "complete_normal_curve_real_cartier_intersection_wellDefined", "related": ["complete_normal_curve_cartier_integral_relation", "complete_normal_curve_cartier_rational_relation", "complete_normal_curve_cartier_real_relation"], "deps": ["integerintersection", "zerointersection", "rcone"], "status": "done", "x": 278, "y": 10450, "paper": "proper"});
nodes.push({"id": "cartierreindex", "title": "Cartier 覆盖重编号：交数不变", "statement": "把实际 Cartier 仿射覆盖改为按环境点编号，实际 Weil 系数和完整正规曲线交数都保持不变。", "scope": "比较两组真实限制；每个点的差别来自实际源 stalk 单位，故所有局部阶数相同。", "inputs": ["k 为任意特征代数闭域；C 为 proper、一维、局部 Noetherian、stalk 整闭的整 Scheme。", "任意真实 Cartier 仿射覆盖；实际完整正规曲线 C→X。"], "steps": [["Cartier 覆盖重编号：交数不变", "比较两组真实限制；每个点的差别来自实际源 stalk 单位，故所有局部阶数相同。", "complete_normal_curve_cartier_intersection_pointIndexed"]], "file": "CartierReindex.lean", "decl": "complete_normal_curve_cartier_intersection_pointIndexed", "related": ["cartierAtlas_pointIndexed_coefficient"], "deps": ["integerintersection"], "status": "done", "x": 278, "y": 10600, "paper": "proper"});
nodes.push({"id": "realpresentation", "title": "任意实 Cartier 表示：交数独立", "statement": "两组生成元及仿射覆盖均可不同；若实组合的实际 Weil 系数相同，则与 C 的交数相同。", "scope": "构造统一的真实点编号覆盖，再放入合并的有限 Cartier 家族并应用已验证的实零关系。后续 normalizedintersection 已完成实际非正规源曲线的正规化与交数。", "inputs": ["k 为任意特征代数闭域；C 为 proper、一维、局部 Noetherian、stalk 整闭的整 Scheme。", "正规、局部 Noetherian 整环境；两组有限真实 Cartier atlases；两个任意实权重向量。"], "steps": [["任意实 Cartier 表示：交数独立", "构造统一的真实点编号覆盖，再放入合并的有限 Cartier 家族并应用已验证的实零关系。后续 normalizedintersection 已完成实际非正规源曲线的正规化与交数。", "complete_normal_curve_real_cartier_presentation_independent"]], "file": "RealIntersectionPresentations.lean", "decl": "complete_normal_curve_real_cartier_presentation_independent", "related": [], "deps": ["realintersectionkernel", "cartierreindex"], "status": "done", "x": 278, "y": 10750, "paper": "proper"});
nodes.push({"id": "realintersectionpositive", "title": "有效实除子：真实交数非负与严格正", "statement": "有效 R-Cartier 除子不包含 C 时交数非负；若还与 C 相交，则交数严格为正。原始 Cartier 权重可有正有负。", "scope": "构造非负有效 Cartier 分解，再用已证明的任意表示独立性识别原始交数。支撑、分解、交数符号都不是额外输入。", "inputs": ["k 为任意特征代数闭域；C 为 proper、一维、局部 Noetherian、stalk 整闭的整 Scheme。", "紧、正规、局部 Noetherian 整环境；实际 Weil 实系数非负；C 不在支撑内。"], "steps": [["有效实除子：真实交数非负与严格正", "构造非负有效 Cartier 分解，再用已证明的任意表示独立性识别原始交数。支撑、分解、交数符号都不是额外输入。", "complete_normal_curve_effective_real_cartier_intersection_signs"]], "file": "EffectiveRealIntersection.lean", "decl": "complete_normal_curve_effective_real_cartier_intersection_signs", "related": [], "deps": ["realpresentation", "rdecomp", "effectiveintersection"], "status": "done", "x": 278, "y": 10900, "paper": "proper"});
nodes.push({"id": "actualpullbackintersection", "title": "实际 Cartier 拉回：交数复合相容", "statement": "对实际 dominant p:Y→X 与 g:C→Y，构造 P=p* A 并证明 P·C=A·(g≫p)。", "scope": "使用实际 stalk 复合及环境函数域映射；包含曲线原本在支撑内的情形。后续 curvenormalization 已完成任意完整整曲线的实际正规化。", "inputs": ["k 为任意特征代数闭域；C 为 proper、一维、局部 Noetherian、stalk 整闭的整 Scheme。", "实际 dominant p；实际完整正规曲线 g；真实环境 CartierAtlas A。"], "steps": [["实际 Cartier 拉回：交数复合相容", "使用实际 stalk 复合及环境函数域映射；包含曲线原本在支撑内的情形。后续 curvenormalization 已完成任意完整整曲线的实际正规化。", "exists_complete_curve_cartier_intersection_pullback"]], "file": "CurveIntersectionPullback.lean", "decl": "exists_complete_curve_cartier_intersection_pullback", "related": ["curve_generic_stalk_pullback_comp"], "deps": ["integerintersection", "cartierpullback"], "status": "done", "x": 278, "y": 11050, "paper": "proper"});
nodes.push({"id": "realpullbackintersection", "title": "实际实 Cartier 拉回：交数相容", "statement": "任意实系数的环境 Cartier 拉回与实际曲线交数相容；若实际曲线像为一个点，实交数为零。", "scope": "逐项构造实际拉回，接通已证明的 Cartier 复合恒等式及点像零值；不要求实权重非负或态射可分。", "inputs": ["k 为任意特征代数闭域；C 为 proper、一维、局部 Noetherian、stalk 整闭的整 Scheme。", "实际 dominant p:Y→X 与 g:C→Y；有限真实 Cartier 生成元与任意实权重。"], "steps": [["实际实 Cartier 拉回：交数相容", "逐项构造实际拉回，接通已证明的 Cartier 复合恒等式及点像零值；不要求实权重非负或态射可分。", "exists_complete_curve_real_cartier_intersection_pullback"]], "file": "RealIntersectionPullback.lean", "decl": "exists_complete_curve_real_cartier_intersection_pullback", "related": ["complete_normal_curve_real_cartier_intersection_point_image_zero"], "deps": ["actualpullbackintersection", "actualintersection", "realintersectionkernel"], "status": "done", "x": 278, "y": 11200, "paper": "proper"});
find('projection').deps.push('realpresentation','realpullbackintersection');
find('projection').scope="实际 Cartier/R-Cartier 交数的主除子移动、整数可加性、任意实表示独立性、点像零值、有效实除子正性和环境拉回复合相容性均已通过。完整正规曲线间的次数倍含不可分次数。尚缺非正规环境曲线的正规化及与实际像曲线／cycle 推出的完整接入；完整环境投影公式仍未完成。";
find('projection').inputs[2]='仍缺：非正规环境曲线的正规化，以及像曲线与 cycle 推出的完整几何识别。实际实交数表示独立性和环境拉回复合相容性已完成。';
find('projection').precise.zh.gap=find('projection').scope;
find('intersection').deps.push('realpresentation','realintersectionpositive');
find('intersection').scope="真实完整正规曲线上的 Cartier/R-Cartier 交数已构造；任意生成元及覆盖的实表示独立性、整数可加性、点像零值和有效实除子正性均已证明。f-nef 数值符号按被压缩完整曲线的定义理解；尚缺非正规曲线的正规化与几何 f-ample 正次数。";
find('intersection').inputs=['已完成：实际实交数、任意生成元／覆盖表示独立性、整数可加性、点像零值和有效实除子交数正性。','尚缺：非正规曲线的正规化，以及几何 f-ample 的正次数。','相对 f-nef 的数值符号按被 f 压缩的完整曲线定义理解。'];
find('intersection').steps=[['真实实交数与表示独立','两组任意实际 Cartier 生成元和覆盖表达同一实 Weil 除子时，交数相同。','complete_normal_curve_real_cartier_presentation_independent'],['有效实除子正性','原始权重可有正有负；通过实际有效分解和表示独立性导出符号。','complete_normal_curve_effective_real_cartier_intersection_signs'],['剩余几何','非正规曲线正规化与几何 f-ample 正次数仍待完成。']];
find('actualintersection').scope='交数由实际 stalk 方程构造，包含曲线原本位于支撑内的情形。后续 realpresentation 已完成任意实表示独立性，realpullbackintersection 完成实际环境拉回相容性；非正规曲线的正规化仍待完成。';
find('projection').precise.en.gap="Actual Cartier/R-Cartier intersection, ambient principal moving, integer additivity, arbitrary real-presentation independence, point-image zero, effective-real-divisor signs and ambient pullback composition are proved. Complete-normal-curve degree includes inseparable maps. Normalization of nonnormal ambient curves and full identification with actual image curves/cycle pushforward remain open. The full ambient projection formula is unfinished.";

// Actual finite normalization and nonnormal curve intersection: formal-26
nodes.push({"id": "finitefrobenius", "title": "有限型 perfect 代数：Frobenius 有限", "statement": "perfect 域 k 上有限型交换代数 A 的每次 Frobenius 迭代都是有限环同态。", "scope": "有限型、perfect 底域和指数特征；不要求域扩张可分。", "inputs": ["有限型、perfect 底域和指数特征；不要求域扩张可分。"], "steps": [["有限型 perfect 代数：Frobenius 有限", "有限型、perfect 底域和指数特征；不要求域扩张可分。", "finiteType_perfectField_iterateFrobenius_finite"]], "file": "FiniteFrobenius.lean", "decl": "finiteType_perfectField_iterateFrobenius_finite", "related": ["frobenius_isIntegral", "finiteType_perfectField_frobenius_finite"], "deps": [], "status": "done", "x": 278, "y": 11600, "paper": "proper"});
nodes.push({"id": "pureclosure", "title": "纯不可分扩张：整闭包有限", "statement": "有限纯不可分扩张 E⊂L 中，若 A 在 E 中的整闭包有限，则 A 在 L 中的整闭包也有限。", "scope": "A 是 perfect 域上的有限型整环；使用实际 Frobenius 映射与扭曲标量的线性嵌入。", "inputs": ["A 是 perfect 域上的有限型整环；使用实际 Frobenius 映射与扭曲标量的线性嵌入。"], "steps": [["纯不可分扩张：整闭包有限", "A 是 perfect 域上的有限型整环；使用实际 Frobenius 映射与扭曲标量的线性嵌入。", "finiteType_perfectField_integralClosure_purelyInseparable_finite"]], "file": "FrobeniusIntegralClosure.lean", "decl": "finiteType_perfectField_integralClosure_purelyInseparable_finite", "related": [], "deps": ["finitefrobenius"], "status": "done", "x": 278, "y": 11750, "paper": "proper"});
nodes.push({"id": "perfectclosure", "title": "正规有限型整环：任意有限扩张的整闭包", "statement": "perfect 域上的正规有限型整环 A，在任意有限分式域扩张 L 中的整闭包是有限 A-模。", "scope": "分解为可分部分与纯不可分部分；迹配对和 Frobenius 分别处理两者。任意特征。", "inputs": ["分解为可分部分与纯不可分部分；迹配对和 Frobenius 分别处理两者。任意特征。"], "steps": [["正规有限型整环：任意有限扩张的整闭包", "分解为可分部分与纯不可分部分；迹配对和 Frobenius 分别处理两者。任意特征。", "finiteType_perfectField_normal_integralClosure_finite"]], "file": "PerfectIntegralClosure.lean", "decl": "finiteType_perfectField_normal_integralClosure_finite", "related": [], "deps": ["pureclosure"], "status": "done", "x": 278, "y": 11900, "paper": "proper"});
nodes.push({"id": "finiteclosure", "title": "任意有限型整环：整闭包有限", "statement": "A 不必正规；A 在任意有限分式域扩张中的整闭包仍为有限 A-模。", "scope": "A 是 perfect 域上的有限型整环；Noether 正规化提供实际多项式子环，再使用整闭包传递性。没有可分性输入。", "inputs": ["A 是 perfect 域上的有限型整环；Noether 正规化提供实际多项式子环，再使用整闭包传递性。没有可分性输入。"], "steps": [["任意有限型整环：整闭包有限", "A 是 perfect 域上的有限型整环；Noether 正规化提供实际多项式子环，再使用整闭包传递性。没有可分性输入。", "finiteType_perfectField_integralClosure_finite"]], "file": "FiniteNormalizationAlgebra.lean", "decl": "finiteType_perfectField_integralClosure_finite", "related": [], "deps": ["perfectclosure"], "status": "done", "x": 278, "y": 12050, "paper": "proper"});
nodes.push({"id": "relativeclosure", "title": "实际相对整闭包：有限性", "statement": "若实际 A-代数 S 嵌入有限分式域扩张 L，则 integralClosure A S 是有限 A-模。", "scope": "构造实际闭包之间的线性嵌入，利用 Noether 性导出有限性；没有假定 S 有限。", "inputs": ["构造实际闭包之间的线性嵌入，利用 Noether 性导出有限性；没有假定 S 有限。"], "steps": [["实际相对整闭包：有限性", "构造实际闭包之间的线性嵌入，利用 Noether 性导出有限性；没有假定 S 有限。", "finiteType_perfectField_relative_integralClosure_finite"]], "file": "RelativeIntegralClosureFinite.lean", "decl": "finiteType_perfectField_relative_integralClosure_finite", "related": [], "deps": ["finiteclosure"], "status": "done", "x": 278, "y": 12200, "paper": "proper"});
nodes.push({"id": "normalizationfinite", "title": "实际 variety 正规化：有限态射", "statement": "perfect 域上局部有限型整 Scheme Y 的实际正规化 ν:Ỹ→Y 是有限态射。", "scope": "正规化取 Y 的泛点 stalk 所定义的 mathlib Scheme；逐个实际仿射开集识别整闭包并验证 finite_app。任意维、任意特征。", "inputs": ["正规化取 Y 的泛点 stalk 所定义的 mathlib Scheme；逐个实际仿射开集识别整闭包并验证 finite_app。任意维、任意特征。"], "steps": [["实际 variety 正规化：有限态射", "正规化取 Y 的泛点 stalk 所定义的 mathlib Scheme；逐个实际仿射开集识别整闭包并验证 finite_app。任意维、任意特征。", "finiteType_perfectField_normalization_isFinite"]], "file": "FiniteNormalizationGeometry.lean", "decl": "finiteType_perfectField_normalization_isFinite", "related": ["generic_stalk_preimage_nonempty_open", "generic_stalk_affine_functionField_embedding"], "deps": ["relativeclosure"], "status": "done", "x": 278, "y": 12350, "paper": "proper"});
nodes.push({"id": "normalizationnormal", "title": "实际正规化：所有 stalk 整闭", "statement": "任意整 Scheme 的泛点正规化，所有实际局部环均整闭。", "scope": "先证明实际仿射坐标环正规，再局部化到每个 stalk。正规性是结论，不是输入；这里不需要有限型假设。", "inputs": ["先证明实际仿射坐标环正规，再局部化到每个 stalk。正规性是结论，不是输入；这里不需要有限型假设。"], "steps": [["实际正规化：所有 stalk 整闭", "先证明实际仿射坐标环正规，再局部化到每个 stalk。正规性是结论，不是输入；这里不需要有限型假设。", "generic_normalization_stalks_normal"]], "file": "GenericNormalizationNormal.lean", "decl": "generic_normalization_stalks_normal", "related": ["relative_integralClosure_isIntegrallyClosed", "generic_normalization_affine_sections_normal"], "deps": ["normalizationfinite"], "status": "done", "x": 278, "y": 12500, "paper": "proper"});
nodes.push({"id": "normalizationbirational", "title": "实际 variety 正规化：双有理", "statement": "ν:Ỹ→Y 在 Y 的某个非空开集上是实际 Scheme 同构。", "scope": "Y 是 perfect 域上局部有限型整 Scheme。将实际泛点截面延拓到开集，再用分离性证明逆态射。", "inputs": ["Y 是 perfect 域上局部有限型整 Scheme。将实际泛点截面延拓到开集，再用分离性证明逆态射。"], "steps": [["实际 variety 正规化：双有理", "Y 是 perfect 域上局部有限型整 Scheme。将实际泛点截面延拓到开集，再用分离性证明逆态射。", "finiteType_perfectField_normalization_birational"]], "file": "GenericNormalizationBirational.lean", "decl": "finiteType_perfectField_normalization_birational", "related": [], "deps": ["normalizationfinite"], "status": "done", "x": 278, "y": 12650, "paper": "proper"});
nodes.push({"id": "curvenormalization", "title": "完整整曲线：正规化性质全部导出", "statement": "完整整曲线的正规化有限、双有理、满射、正规、仍一维、局部 Noetherian，并在底域上 proper。", "scope": "k 为任意特征代数闭域；原曲线只假定完整、整、一维，不假定光滑或正规。所有列出的性质均已证明。", "inputs": ["k 为任意特征代数闭域；原曲线只假定完整、整、一维，不假定光滑或正规。所有列出的性质均已证明。"], "steps": [["完整整曲线：正规化性质全部导出", "k 为任意特征代数闭域；原曲线只假定完整、整、一维，不假定光滑或正规。所有列出的性质均已证明。", "complete_integral_curve_normalization_properties"]], "file": "CurveNormalization.lean", "decl": "complete_integral_curve_normalization_properties", "related": ["generic_normalization_dimension_le_one", "finiteType_perfectField_normalization_surjective"], "deps": ["normalizationfinite", "normalizationnormal", "normalizationbirational"], "status": "done", "x": 278, "y": 12800, "paper": "proper"});
nodes.push({"id": "normalizedintersection", "title": "非正规曲线：真实实交数与表示独立", "statement": "在实际正规化上按局部阶数定义 D·C；任意实 Cartier 生成元及覆盖的表示独立，点像交数为零。", "scope": "C 是任意完整整曲线；k 为任意特征代数闭域。表示独立要求环境 Scheme 正规且局部 Noetherian。", "inputs": ["C 是任意完整整曲线；k 为任意特征代数闭域。表示独立要求环境 Scheme 正规且局部 Noetherian。"], "steps": [["非正规曲线：真实实交数与表示独立", "C 是任意完整整曲线；k 为任意特征代数闭域。表示独立要求环境 Scheme 正规且局部 Noetherian。", "complete_integral_curve_real_cartier_presentation_independent"]], "file": "NormalizedCurveIntersection.lean", "decl": "complete_integral_curve_real_cartier_presentation_independent", "related": ["complete_integral_curve_real_intersection_point_image_zero"], "deps": ["curvenormalization", "realpresentation"], "status": "done", "x": 278, "y": 12950, "paper": "proper"});
nodes.push({"id": "normalizedsigns", "title": "非正规曲线：有效实除子交数正性", "statement": "有效 R-Cartier 除子不包含 C 时 D·C≥0；若还与 C 相交，则 D·C>0。", "scope": "正规、局部 Noetherian、紧的实际环境；C 是完整整曲线，可非正规。由正规化的实际满射传递支撑相交。", "inputs": ["正规、局部 Noetherian、紧的实际环境；C 是完整整曲线，可非正规。由正规化的实际满射传递支撑相交。"], "steps": [["非正规曲线：有效实除子交数正性", "正规、局部 Noetherian、紧的实际环境；C 是完整整曲线，可非正规。由正规化的实际满射传递支撑相交。", "complete_integral_curve_effective_real_intersection_signs"]], "file": "NormalizedIntersectionSigns.lean", "decl": "complete_integral_curve_effective_real_intersection_signs", "related": [], "deps": ["normalizedintersection", "realintersectionpositive"], "status": "done", "x": 278, "y": 13100, "paper": "proper"});
nodes.push({"id": "normalizedpullback", "title": "非正规曲线：真实实拉回交数相容", "statement": "构造实际 P=p*D，并证明 P·C=D·(g≫p)，包含任意实系数及曲线位于支撑内的情形。", "scope": "p:Y→X 为实际 dominant 态射；g:C→Y 为任意实际态射；C 是完整整曲线。这里只是拉回复合公式，不是全部 cycle 射影公式。", "inputs": ["p:Y→X 为实际 dominant 态射；g:C→Y 为任意实际态射；C 是完整整曲线。这里只是拉回复合公式，不是全部 cycle 射影公式。"], "steps": [["非正规曲线：真实实拉回交数相容", "p:Y→X 为实际 dominant 态射；g:C→Y 为任意实际态射；C 是完整整曲线。这里只是拉回复合公式，不是全部 cycle 射影公式。", "exists_complete_integral_curve_real_intersection_pullback"]], "file": "NormalizedIntersectionPullback.lean", "decl": "exists_complete_integral_curve_real_intersection_pullback", "related": [], "deps": ["normalizedintersection", "realpullbackintersection"], "status": "done", "x": 278, "y": 13250, "paper": "proper"});
nodes.push({"id": "fieldfunctoriality", "title": "实际函数域映射：复合相容", "statement": "dominant g:C→Y、f:Y→X 的实际函数域映射满足 (f∘g)*=g*∘f*。", "scope": "三个实际整 Scheme；由仿射截面 germ 与实际 stalk 方块证明。", "inputs": ["三个实际整 Scheme；由仿射截面 germ 与实际 stalk 方块证明。"], "steps": [["实际函数域映射：复合相容", "三个实际整 Scheme；由仿射截面 germ 与实际 stalk 方块证明。", "dominantFunctionFieldMap_comp"]], "file": "FunctionFieldFunctoriality.lean", "decl": "dominantFunctionFieldMap_comp", "related": [], "deps": ["cartierpullback"], "status": "done", "x": 278, "y": 13400, "paper": "proper"});
nodes.push({"id": "normalizeddegree", "title": "非正规源曲线：Cartier 次数公式", "statement": "(f*D)·C=[k(C):k(X)] deg_X(D)，源曲线可非正规，X 为完整正规曲线。", "scope": "f 为 proper dominant 曲线态射；k 为任意特征代数闭域。正规化的实际泛点同构识别原函数域；使用含不可分部分的全次数。非正规目标的实际正规化提升和次数不变现已完成；沿提升的限制相容性仍需接入。", "inputs": ["f 为 proper dominant 曲线态射；k 为任意特征代数闭域。正规化的实际泛点同构识别原函数域；使用含不可分部分的全次数。非正规目标的实际正规化提升和次数不变现已完成；沿提升的限制相容性仍需接入。"], "steps": [["非正规源曲线：Cartier 次数公式", "f 为 proper dominant 曲线态射；k 为任意特征代数闭域。正规化的实际泛点同构识别原函数域；使用含不可分部分的全次数。非正规目标的实际正规化提升和次数不变现已完成；沿提升的限制相容性仍需接入。", "complete_integral_curve_cartier_intersection_degree"]], "file": "NormalizedCurveDegree.lean", "decl": "complete_integral_curve_cartier_intersection_degree", "related": [], "deps": ["normalizedintersection", "fieldfunctoriality", "curveintersectiondegree"], "status": "done", "x": 278, "y": 13550, "paper": "proper"});
nodes.push({"id": "normalizedrealdegree", "title": "非正规源曲线：任意实 Cartier 次数公式", "statement": "任意实 Cartier 组合满足同一全函数域次数公式，实权重无需非负。", "scope": "实际完整整源曲线与完整正规目标曲线；proper dominant 映射，任意特征。逐项使用已验证的实际整数次数公式。", "inputs": ["实际完整整源曲线与完整正规目标曲线；proper dominant 映射，任意特征。逐项使用已验证的实际整数次数公式。"], "steps": [["非正规源曲线：任意实 Cartier 次数公式", "实际完整整源曲线与完整正规目标曲线；proper dominant 映射，任意特征。逐项使用已验证的实际整数次数公式。", "complete_integral_curve_real_cartier_intersection_degree"]], "file": "NormalizedRealDegree.lean", "decl": "complete_integral_curve_real_cartier_intersection_degree", "related": [], "deps": ["normalizeddegree"], "status": "done", "x": 278, "y": 13700, "paper": "proper"});
nodes.push({"id": "normalnormalization", "title": "正规 variety：正规化是同构", "statement": "若 Y 已正规，则其实际正规化 ν:Ỹ→Y 是 Scheme 同构。", "scope": "Y 是 perfect 域上局部有限型整 Scheme，所有实际 stalk 整闭；有限性和双有理性从已证明的正规化构造导出。", "inputs": ["Y 是 perfect 域上局部有限型整 Scheme，所有实际 stalk 整闭；有限性和双有理性从已证明的正规化构造导出。"], "steps": [["正规 variety：正规化是同构", "Y 是 perfect 域上局部有限型整 Scheme，所有实际 stalk 整闭；有限性和双有理性从已证明的正规化构造导出。", "finiteType_perfectField_normal_normalization_isIso"]], "file": "NormalNormalization.lean", "decl": "finiteType_perfectField_normal_normalization_isIso", "related": [], "deps": ["normalizationfinite", "normalizationbirational", "normalfinite"], "status": "done", "x": 278, "y": 13850, "paper": "proper"});
find('projection').deps.push('normalizedintersection','normalizedpullback','normalizedrealdegree');
find('projection').scope="任意完整整源曲线的实际正规化、Cartier/R-Cartier 交数、表示独立、有效除子正性、点像零值和环境拉回复合都已验证。源曲线可非正规；到完整正规目标曲线的次数公式使用原函数域的全次数。仍缺到非正规像曲线的正规化提升／相容性，以及像曲线与实际 cycle 推出的完整识别；完整环境射影公式尚未完成。";
find('projection').inputs[2]='尚缺：非正规像曲线的正规化提升及 cycle 推出识别。实际曲线正规化、源可非正规的次数公式和实交数均已完成。';
find('projection').precise.zh.gap=find('projection').scope;
find('intersection').deps.push('normalizedintersection','normalizedsigns');
find('intersection').scope="实际 Cartier/R-Cartier 交数已在任意完整整曲线上通过真实正规化构造；表示独立、整数可加性、点像零值、有效除子非负及严格正性均已证明。相对 f-nef 的数值条件按被压缩完整曲线定义理解。剩余缺口是几何 f-ample 的正次数，并非交数定义或曲线正规化。";
find('intersection').inputs=['已完成：任意完整整曲线的实际正规化、真实实交数与表示独立、点像零值、有效除子交数正性。','尚缺：从几何 f-ample 导出压缩完整曲线上的严格正次数。','相对 f-nef 的数值条件只作用于被 f 压缩的完整曲线。'];
find('intersection').steps=[['任意完整整曲线的正规化','实际正规化有限、双有理、正规、满射，仍完整且一维。','complete_integral_curve_normalization_properties'],['真实实交数与正性','在实际正规化上求局部阶数；表示独立和有效除子交数符号均已验证。','complete_integral_curve_effective_real_intersection_signs'],['剩余几何 ample 正性','从几何 f-ample 导出压缩曲线上严格正次数，仍待完成。']];
find('actualintersection').scope='原完整正规曲线上的交数已选择无关。后续 normalizedintersection 已对任意完整整曲线构造实际正规化并证明任意实表示独立；normalizedpullback 完成环境拉回复合。';
find('projection').precise.en.gap="Actual normalization, Cartier/R-Cartier intersection, presentation independence, effective-divisor signs, point-image zero and ambient pullback composition are proved for every complete integral source curve, including nonnormal curves. The degree formula to a complete normal target uses the original full function-field degree. Lifting to the normalization of a nonnormal image curve and full actual image-curve/cycle identification remain open; the full ambient projection formula is unfinished.";

// Actual normalization lifting and unchanged full degree: formal-27
nodes.push({"id": "finitefunctionfield", "title": "实际有限 dominant 映射：函数域扩张有限", "statement": "实际有限 dominant 态射 f:C→X 诱导有限函数域扩张 k(X)⊂k(C)。", "scope": "C、X 为任意整 Scheme；不要求正规、可分或一维。从实际仿射环的有限性和局部化推导。", "inputs": ["C、X 为任意整 Scheme；不要求正规、可分或一维。从实际仿射环的有限性和局部化推导。"], "steps": [["实际有限 dominant 映射：函数域扩张有限", "C、X 为任意整 Scheme；不要求正规、可分或一维。从实际仿射环的有限性和局部化推导。", "finite_dominant_functionField_finite"]], "file": "FiniteFunctionField.lean", "decl": "finite_dominant_functionField_finite", "related": [], "deps": ["cartierpullback"], "status": "done", "x": 278, "y": 14300, "paper": "proper"});
nodes.push({"id": "relativefieldnormalization", "title": "在实际源函数域中正规化：有限", "statement": "将实际有限 dominant 映射的目标在 k(C) 中正规化，得到的实际相对正规化仍有限。", "scope": "目标是 perfect 域上的局部有限型整 Scheme；包含非正规目标和不可分函数域扩张。", "inputs": ["目标是 perfect 域上的局部有限型整 Scheme；包含非正规目标和不可分函数域扩张。"], "steps": [["在实际源函数域中正规化：有限", "目标是 perfect 域上的局部有限型整 Scheme；包含非正规目标和不可分函数域扩张。", "finiteType_perfectField_relative_generic_normalization_isFinite"]], "file": "RelativeFieldNormalization.lean", "decl": "finiteType_perfectField_relative_generic_normalization_isFinite", "related": [], "deps": ["finitefunctionfield", "relativeclosure"], "status": "done", "x": 278, "y": 14450, "paper": "proper"});
nodes.push({"id": "relativenormalidentity", "title": "正规有限源：识别实际相对正规化", "statement": "有限 dominant 态射的正规源 C，就是目标在 k(C) 中的实际相对正规化。比较态射是 Scheme 同构。", "scope": "从实际泛点截面延拓，证明比较态射有限、双有理，再用源正规性得到同构；比较同构不是 input。", "inputs": ["从实际泛点截面延拓，证明比较态射有限、双有理，再用源正规性得到同构；比较同构不是 input。"], "steps": [["正规有限源：识别实际相对正规化", "从实际泛点截面延拓，证明比较态射有限、双有理，再用源正规性得到同构；比较同构不是 input。", "finiteType_perfectField_relative_normalization_source_isIso"]], "file": "RelativeNormalizationIdentification.lean", "decl": "finiteType_perfectField_relative_normalization_source_isIso", "related": ["finite_dominant_generic_section_birational"], "deps": ["relativefieldnormalization", "normalfinite"], "status": "done", "x": 278, "y": 14600, "paper": "proper"});
nodes.push({"id": "normalizationlift", "title": "正规源到非正规目标：实际正规化提升", "statement": "构造 l:C→X̃，使 l≫ν_X=f；并证明 l 有限且 dominant。", "scope": "f 是实际有限 dominant 态射，C 正规；X 是 perfect 域上的局部有限型整 Scheme，可非正规。利用实际函数域 Spec 方块和正规化泛性质。", "inputs": ["f 是实际有限 dominant 态射，C 正规；X 是 perfect 域上的局部有限型整 Scheme，可非正规。利用实际函数域 Spec 方块和正规化泛性质。"], "steps": [["正规源到非正规目标：实际正规化提升", "f 是实际有限 dominant 态射，C 正规；X 是 perfect 域上的局部有限型整 Scheme，可非正规。利用实际函数域 Spec 方块和正规化泛性质。", "exists_finite_dominant_normalization_lift"]], "file": "NormalizationLift.lean", "decl": "exists_finite_dominant_normalization_lift", "related": ["dominant_functionField_Spec_square"], "deps": ["relativenormalidentity"], "status": "done", "x": 278, "y": 14750, "paper": "proper"});
nodes.push({"id": "curvenormalizationlift", "title": "任意整曲线：正规化交换图与次数不变", "statement": "proper dominant f:C→X 提升为有限 dominant f̃:C̃→X̃，ν_C≫f=f̃≫ν_X，且 [k(C̃):k(X̃)]=[k(C):k(X)]。", "scope": "C、X 都是任意特征代数闭域上的完整整曲线，两者均可非正规、不光滑。实际交换图和全函数域次数相等均已证明，保留不可分部分。", "inputs": ["C、X 都是任意特征代数闭域上的完整整曲线，两者均可非正规、不光滑。实际交换图和全函数域次数相等均已证明，保留不可分部分。"], "steps": [["任意整曲线：正规化交换图与次数不变", "C、X 都是任意特征代数闭域上的完整整曲线，两者均可非正规、不光滑。实际交换图和全函数域次数相等均已证明，保留不可分部分。", "complete_integral_curves_normalization_lift_degree"]], "file": "CurveNormalizationLift.lean", "decl": "complete_integral_curves_normalization_lift_degree", "related": ["birational_functionFieldMap_bijective"], "deps": ["normalizationlift", "curvenormalization", "propercurvefinite", "fieldfunctoriality"], "status": "done", "x": 278, "y": 14900, "paper": "proper"});
find('projection').deps.push('curvenormalizationlift');
find('projection').scope="任意完整整曲线的实际有限正规化、实交数、表示独立、正性、点像零值和环境拉回复合已验证。任意 proper dominant 曲线态射已构造实际正规化提升，交换图和原函数域全次数不变均已验证。剩余：曲线局部限制沿此提升的相容性，以及实际像曲线／cycle 推出的完整识别。完整环境射影公式仍未完成。";
find('projection').inputs[2]='尚缺：局部曲线限制沿正规化提升的相容性，以及实际像曲线和 cycle 推出的完整识别。实际正规化提升与全函数域次数不变已经完成。';
find('projection').precise.zh.gap=find('projection').scope;
find('projection').precise.en.gap="Actual finite normalization, real intersection, presentation independence, signs, point-image zero and ambient pullback composition are proved for arbitrary complete integral curves. Every proper dominant curve map now has an actual normalization lift, commuting square and unchanged original full function-field degree. Remaining: local curve-restriction compatibility along this lift and full actual image-curve/cycle identification. The full ambient projection formula is unfinished.";

// Actual ambient projection formula, formal-28
nodes.push({"id": "curverestrictioncomposition", "title": "实际曲线限制：沿映射复合相容", "statement": "实际 Cartier 曲线限制沿 proper dominant 曲线映射相容，交数乘以完整函数域次数。", "scope": "由实际泛点 stalk 单位、方程和 DVR 阶数证明；环境曲线映射可不 dominant，曲线也可包含于原除子支撑。", "inputs": ["由实际泛点 stalk 单位、方程和 DVR 阶数证明；环境曲线映射可不 dominant，曲线也可包含于原除子支撑。"], "steps": [["实际曲线限制：沿映射复合相容", "由实际泛点 stalk 单位、方程和 DVR 阶数证明；环境曲线映射可不 dominant，曲线也可包含于原除子支撑。", "complete_normal_curve_cartier_intersection_reparametrization"]], "file": "CurveRestrictionComposition.lean", "decl": "complete_normal_curve_cartier_intersection_reparametrization", "related": ["dominant_curve_generic_unit_comp", "generic_unit_transport_functionField"], "deps": ["actualintersection", "propercurveglobal"], "status": "done", "x": 278, "y": 15100, "paper": "proper"});
nodes.push({"id": "integralcurveprojection", "title": "非正规整曲线：Cartier 射影公式", "statement": "两条完整整曲线均可非正规：I_C(f≫j,A)=[k(C):k(Y)] I_Y(j,A)。", "scope": "使用实际正规化提升与限制复合相容；任意特征代数闭域，保留不可分全次数，不输入交数兼容等式。", "inputs": ["使用实际正规化提升与限制复合相容；任意特征代数闭域，保留不可分全次数，不输入交数兼容等式。"], "steps": [["非正规整曲线：Cartier 射影公式", "使用实际正规化提升与限制复合相容；任意特征代数闭域，保留不可分全次数，不输入交数兼容等式。", "complete_integral_curve_cartier_projection"]], "file": "IntegralCurveProjection.lean", "decl": "complete_integral_curve_cartier_projection", "related": [], "deps": ["curverestrictioncomposition", "curvenormalizationlift"], "status": "done", "x": 278, "y": 15250, "paper": "proper"});
nodes.push({"id": "realintegralcurveprojection", "title": "非正规整曲线：实 Cartier 射影公式", "statement": "任意有限组实际 Cartier 除子的实线性组合满足同一曲线次数公式。", "scope": "实权重可正、负或零；原曲线不要求正规、光滑，映射不要求可分。", "inputs": ["实权重可正、负或零；原曲线不要求正规、光滑，映射不要求可分。"], "steps": [["非正规整曲线：实 Cartier 射影公式", "实权重可正、负或零；原曲线不要求正规、光滑，映射不要求可分。", "complete_integral_curve_real_cartier_projection"]], "file": "RealIntegralCurveProjection.lean", "decl": "complete_integral_curve_real_cartier_projection", "related": [], "deps": ["integralcurveprojection"], "status": "done", "x": 278, "y": 15400, "paper": "proper"});
nodes.push({"id": "curvecycleprojection", "title": "实际曲线 cycle：推出与交数相容", "statement": "以真实 Order.height 作维数权重，实际泛点 cycle 的推出重数等于函数域全次数。", "scope": "实际剩余域与泛点函数域的识别已证明，交数相容也已证明；这里没有 hcompat 输入。", "inputs": ["实际剩余域与泛点函数域的识别已证明，交数相容也已证明；这里没有 hcompat 输入。"], "steps": [["实际曲线 cycle：推出与交数相容", "实际剩余域与泛点函数域的识别已证明，交数相容也已证明；这里没有 hcompat 输入。", "complete_integral_curve_actual_cycle_projection"]], "file": "CurveCycleProjection.lean", "decl": "complete_integral_curve_actual_cycle_projection", "related": ["dominant_generic_residueDegree_functionField", "curve_generic_height_preserved"], "deps": ["realintegralcurveprojection", "geomcycle"], "status": "done", "x": 278, "y": 15550, "paper": "proper"});
nodes.push({"id": "curveimagegeometry", "title": "实际像 Scheme：整、完整且至多一维", "statement": "从完整整曲线 C→X 构造实际 scheme-theoretic image，证明整性、proper 性与维数上界。", "scope": "X 是分离、局部有限型环境；实际像的仿射环约化、满射和闭点性质均从映射推出，不预设像曲线。", "inputs": ["X 是分离、局部有限型环境；实际像的仿射环约化、满射和闭点性质均从映射推出，不预设像曲线。"], "steps": [["实际像 Scheme：整、完整且至多一维", "X 是分离、局部有限型环境；实际像的仿射环约化、满射和闭点性质均从映射推出，不预设像曲线。", "complete_integral_curve_actual_image_properties"]], "file": "CurveImageGeometry.lean", "decl": "complete_integral_curve_actual_image_properties", "related": ["actual_image_isReduced", "proper_integral_actual_image_isIntegral"], "deps": ["curvecycleprojection"], "status": "done", "x": 278, "y": 15700, "paper": "proper"});
nodes.push({"id": "curveimagecases", "title": "实际像：点／曲线二择一与点像零值", "statement": "实际像要么只有一个点且交数为零，要么是一维完整整曲线。", "scope": "从实际维数上界推出二择一；闭浸入保持点闭包的实际维数权重。", "inputs": ["从实际维数上界推出二择一；闭浸入保持点闭包的实际维数权重。"], "steps": [["实际像：点／曲线二择一与点像零值", "从实际维数上界推出二择一；闭浸入保持点闭包的实际维数权重。", "complete_integral_curve_actual_image_dichotomy"]], "file": "CurveImageCases.lean", "decl": "complete_integral_curve_actual_image_dichotomy", "related": ["closedImmersion_height_eq", "integral_scheme_point_or_curve"], "deps": ["curveimagegeometry", "normalizedintersection"], "status": "done", "x": 278, "y": 15850, "paper": "proper"});
nodes.push({"id": "imagecyclemultiplicity", "title": "环境 cycle 重数：实际像的全函数域次数", "statement": "环境中实际 cycle 推出的泛点重数等于 [k(C):k(image C)]。", "scope": "实际闭浸入的剩余域映射是同构，推出重数与实际像的函数域次数一致；不是额外兼容假设。", "inputs": ["实际闭浸入的剩余域映射是同构，推出重数与实际像的函数域次数一致；不是额外兼容假设。"], "steps": [["环境 cycle 重数：实际像的全函数域次数", "实际闭浸入的剩余域映射是同构，推出重数与实际像的函数域次数一致；不是额外兼容假设。", "actual_image_residueDegree_functionField"]], "file": "ImageCycleMultiplicity.lean", "decl": "actual_image_residueDegree_functionField", "related": ["closedImmersion_residueFieldMap_bijective", "residueDegree_comp_closedImmersion"], "deps": ["curveimagecases"], "status": "done", "x": 278, "y": 16000, "paper": "proper"});
nodes.push({"id": "ambientprojection", "title": "真实环境射影公式：任意实系数", "statement": "将实际像、维数下降、全次数和交数公式合并，证明 D·C=D·push[C] 的环境相容性。", "scope": "交数用实际正规化上的局部阶数；像为点时为零，像为非正规曲线时也已覆盖。", "inputs": ["交数用实际正规化上的局部阶数；像为点时为零，像为非正规曲线时也已覆盖。"], "steps": [["真实环境射影公式：任意实系数", "交数用实际正规化上的局部阶数；像为点时为零，像为非正规曲线时也已覆盖。", "complete_integral_curve_ambient_real_projection"]], "file": "AmbientCurveProjection.lean", "decl": "complete_integral_curve_ambient_real_projection", "related": [], "deps": ["imagecyclemultiplicity", "realintegralcurveprojection"], "status": "done", "x": 278, "y": 16150, "paper": "proper"});
nodes.push({"id": "actualprojectionformula", "title": "实际拉回与环境 cycle：射影公式", "statement": "构造实际 Cartier 拉回 P=p*D，并证明 P·C=D·(p∘g)_*[C]。", "scope": "任意完整整曲线的实际映射 g；所有支撑移动、正规化、实线性扩展及 cycle 重数均已接通。", "inputs": ["任意完整整曲线的实际映射 g；所有支撑移动、正规化、实线性扩展及 cycle 重数均已接通。"], "steps": [["实际拉回与环境 cycle：射影公式", "任意完整整曲线的实际映射 g；所有支撑移动、正规化、实线性扩展及 cycle 重数均已接通。", "exists_complete_integral_curve_actual_real_projection_formula"]], "file": "ActualProjectionFormula.lean", "decl": "exists_complete_integral_curve_actual_real_projection_formula", "related": [], "deps": ["ambientprojection", "normalizedpullback"], "status": "done", "x": 278, "y": 16300, "paper": "proper"});
Object.assign(find('projection'),{"status": "done", "file": "EmbeddedCurveProjection.lean", "decl": "exists_embedded_complete_curve_real_projection_formula", "related": ["residueDegree_precomp_closedImmersion", "embedded_curve_actual_cycle_push"], "deps": ["actualprojectionformula"], "scope": "已完成实际环境射影公式 (p*D)·C=D·p_*[C]。C 是实际嵌入的完整整曲线；D 为任意实 Cartier 组合；交数按实际正规化上的局部阶数定义，推出为 mathlib 的实际环境 cycle。像曲线可非正规，次数包含不可分部分；像为点时交数与推出均为零。没有交数相容、正规化或像曲线 input。完整 negativity lemma 的其他几何步骤仍未完成。", "inputs": ["k 为任意特征代数闭域；X、Y 整，X 为分离、局部有限型 k-Scheme。", "p:Y→X 实际 dominant 且 quasi-compact；g:C↪Y 实际闭浸入；C 完整整且一维，可非正规。", "D 是有限实际 Cartier 生成元的任意实线性组合；P 的实际拉回方程由定理构造。"], "steps": [["构造实际拉回", "构造 p*D 的实际图表、局部方程并证明交数复合相容。", "exists_complete_integral_curve_real_intersection_pullback"], ["实际像与分情况", "证明实际像整、完整且至多一维，推出点／曲线二择一。", "complete_integral_curve_actual_image_dichotomy"], ["实际重数与局部阶数", "识别环境 cycle 重数与实际像的全函数域次数，合并局部阶数公式。", "complete_integral_curve_ambient_real_projection"], ["嵌入曲线的射影公式", "已完成实际环境射影公式 (p*D)·C=D·p_*[C]。C 是实际嵌入的完整整曲线；D 为任意实 Cartier 组合；交数按实际正规化上的局部阶数定义，推出为 mathlib 的实际环境 cycle。像曲线可非正规，次数包含不可分部分；像为点时交数与推出均为零。没有交数相容、正规化或像曲线 input。完整 negativity lemma 的其他几何步骤仍未完成。", "exists_embedded_complete_curve_real_projection_formula"]]});
find('projection').precise.zh.gap=find('projection').scope;
find('projection').precise.en.gap="The actual ambient projection formula (p*D)\u00b7C=D\u00b7p_*[C] is proved for actual embedded complete integral curves and arbitrary real Cartier combinations. Intersection uses local orders on the actual normalization; pushforward is the actual mathlib ambient cycle. Image curves may be nonnormal and degree includes inseparable parts; point images give zero intersection and zero pushforward. No intersection compatibility, normalization or image-curve input is assumed. Other geometric steps of the full negativity lemma remain open.";

find('projection').statement='(π*D)·Γ = D·π_*[Γ] 已在真实除子、曲线与环境 cycle 上证明，包含点像与非正规曲线像。';

// Actual relative nef pullback and cycle cases, formal-29
nodes.push({"id": "fixedpullbackintersection", "title": "固定实际拉回：所有曲线的交数相容", "statement": "任意符合实际拉回方程的同一个 Cartier atlas，对每条完整正规整曲线都满足交数复合公式。", "scope": "依据真实局部方程与 stalk 映射证明；不要求对不同曲线另选不同拉回。", "inputs": ["依据真实局部方程与 stalk 映射证明；不要求对不同曲线另选不同拉回。"], "steps": [["固定实际拉回：所有曲线的交数相容", "依据真实局部方程与 stalk 映射证明；不要求对不同曲线另选不同拉回。", "complete_curve_cartier_intersection_of_actual_pullback"]], "file": "FixedCartierPullbackIntersection.lean", "decl": "complete_curve_cartier_intersection_of_actual_pullback", "related": [], "deps": ["actualpullbackintersection"], "status": "done", "x": 278, "y": 16600, "paper": "proper"});
nodes.push({"id": "canonicalrealpullback", "title": "统一实际实拉回：任意完整整曲线", "statement": "固定 P=p*D，与任意完整整曲线的交数均与环境映射复合相容。", "scope": "非正规曲线、位于原支撑内的曲线和任意实权重均包含。P 的图表与有理方程实际构造，独立于测试曲线。", "inputs": ["非正规曲线、位于原支撑内的曲线和任意实权重均包含。P 的图表与有理方程实际构造，独立于测试曲线。"], "steps": [["统一实际实拉回：任意完整整曲线", "非正规曲线、位于原支撑内的曲线和任意实权重均包含。P 的图表与有理方程实际构造，独立于测试曲线。", "complete_integral_curve_canonical_real_pullback_intersection"]], "file": "CanonicalRealPullbackIntersection.lean", "decl": "complete_integral_curve_canonical_real_pullback_intersection", "related": ["actualCartierPullback_data"], "deps": ["fixedpullbackintersection", "normalizedintersection"], "status": "done", "x": 278, "y": 16750, "paper": "proper"});
Object.assign(find('nefpull'),{"title": "真实相对 nef 的拉回保持", "statement": "D 为 f-nef，则同一个实际拉回 p*D 为 (p≫f)-nef。", "scope": "相对 nef 直接定义在被真实态射压缩的完整整曲线上，交数为实际正规化上的局部阶数。统一实际拉回 P 对所有曲线保持相对 nef 性。实际像的完整性、被压缩条件及次数倍数均已证明，无交数相容或 nef 传递 input。", "status": "done", "file": "ActualRelativeNef.lean", "decl": "actual_relative_nef_canonical_pullback", "related": ["actual_relative_nef_negative_iff"], "deps": ["canonicalrealpullback", "projection", "curveimagecases"], "inputs": ["任意特征代数闭域；X、Y 整；X 分离、局部有限型。", "实际 dominant p:Y→X 与 f:X→S；任意有限实际 Cartier 生成元和任意实权重。", "f-nef 是真实测试曲线上的定义性条件，不是额外传递假设。"], "steps": [["相对定义", "只在被真实态射压缩的完整整曲线上检验真实交数。", "actual_relative_nef_negative_iff"], ["统一拉回保持", "相对 nef 直接定义在被真实态射压缩的完整整曲线上，交数为实际正规化上的局部阶数。统一实际拉回 P 对所有曲线保持相对 nef 性。实际像的完整性、被压缩条件及次数倍数均已证明，无交数相容或 nef 传递 input。", "actual_relative_nef_canonical_pullback"]]});
Object.assign(find('projectioncases'),{"title": "真实 cycle 射影公式的两种情形", "statement": "实际点像推出为零；实际曲线像按完整函数域次数推出，真实实交数满足对应等式。", "scope": "实际像要么是点，此时真实交数与环境曲线 cycle 推出都为零；要么是完整整曲线，此时实际推出重数为到像的完整函数域次数。像曲线可非正规，包含不可分次数；没有 hcompat 或像曲线可测试性 input。", "status": "done", "file": "ActualCycleProjectionCases.lean", "decl": "actual_complete_curve_cycle_projection_cases", "related": ["actual_point_image_curve_cycle_zero"], "deps": ["projection", "imagecyclemultiplicity"], "inputs": ["完整整曲线 C→X；X 为分离、局部有限型整环境。", "任意特征代数闭域，任意实际 Cartier 家族与实权重；实际维数权重 Order.height。"], "steps": [["点像的 cycle 零值", "从实际像只有一点与维数权重下降证明真实 cycle 推出为零。", "actual_point_image_curve_cycle_zero"], ["两种实际情形", "实际像要么是点，此时真实交数与环境曲线 cycle 推出都为零；要么是完整整曲线，此时实际推出重数为到像的完整函数域次数。像曲线可非正规，包含不可分次数；没有 hcompat 或像曲线可测试性 input。", "actual_complete_curve_cycle_projection_cases"]]});
find('chow').deps.push('normalizationfinite','projection','nefpull');
find('chow').scope='有限正规化、实际全局曲线射影公式、相对 nef 拉回、实际 R-Cartier 推拉及有效支撑拉回均已完成。Chow 节点仍缺 Hartshorne 有限覆盖构造的相对射影性；纤维二择一仍依赖独立的高维曲线选择与连通性证明。';
find('chow').inputs=['已完成：实际图像闭包的 proper、双有理与满射。','待完成：Hartshorne 有限仿射覆盖构造的相对射影性。','已完成：实际有限正规化、真实 R-Cartier 支撑与推拉、实际射影公式及相对 nef 保持。'];
find('chow').steps[2]=['正规化与几何公式：已完成','实际有限正规化、实际环境射影公式、相对 nef 拉回及 R-Cartier 几何推拉已验证。完整 Chow 射影性仍待完成。','finiteType_perfectField_normalization_isFinite'];
find('intersection').deps.push('nefpull');

// Actual exceptional curve coverage and zero-prime curve, formal-30
nodes.push({"id": "affinelinepoint", "title": "仿射直线通过指定点", "statement": "多项式环中实际构造严格包含于点极大理想的素理想，商环同构于 k[T]。", "scope": "显式取一坐标为 T，其余为点的坐标；限制映射满射，其核给所需直线。", "inputs": ["显式取一坐标为 T，其余为点的坐标；限制映射满射，其核给所需直线。"], "steps": [["仿射直线通过指定点", "显式取一坐标为 T，其余为点的坐标；限制映射满射，其核给所需直线。", "affine_line_kernel_below_point"]], "file": "AffineLineThroughPoint.lean", "decl": "affine_line_kernel_below_point", "related": [], "deps": [], "status": "done", "x": 278, "y": 17000, "paper": "projective"});
nodes.push({"id": "affinecurvepoint", "title": "仿射整曲线通过指定闭点", "statement": "正维有限型整仿射簇中，构造严格包含于指定极大理想的素理想 P，实际商环维数为 1。", "scope": "任意特征代数闭域。Noether 正规化、直线及 going-down 给 P；积分扩张证明维数上界与非域性。没有曲线存在性 input。", "inputs": ["任意特征代数闭域。Noether 正规化、直线及 going-down 给 P；积分扩张证明维数上界与非域性。没有曲线存在性 input。"], "steps": [["仿射整曲线通过指定闭点", "任意特征代数闭域。Noether 正规化、直线及 going-down 给 P；积分扩张证明维数上界与非域性。没有曲线存在性 input。", "affine_integral_curve_through_maximal"]], "file": "AffineCurveThroughPoint.lean", "decl": "affine_integral_curve_through_maximal", "related": ["integral_extension_krullDimLE_one"], "deps": ["affinelinepoint"], "status": "done", "x": 278, "y": 17150, "paper": "projective"});
nodes.push({"id": "functionfielddimension", "title": "实际函数域超越次数控制维数", "statement": "有限型整 Scheme 的实际函数域超越次数至多 1，则 Scheme 的 Krull 维数至多 1。", "scope": "逐实际仿射图应用 Noether 正规化和积分扩张，再用实际 coheight 拼接全局维数。", "inputs": ["逐实际仿射图应用 Noether 正规化和积分扩张，再用实际 coheight 拼接全局维数。"], "steps": [["实际函数域超越次数控制维数", "逐实际仿射图应用 Noether 正规化和积分扩张，再用实际 coheight 拼接全局维数。", "integral_scheme_dimension_of_functionField_trdeg_le_one"]], "file": "FunctionFieldDimension.lean", "decl": "integral_scheme_dimension_of_functionField_trdeg_le_one", "related": ["finiteType_domain_dimension_of_trdeg_le_one", "affine_chart_dimension_of_functionField_trdeg_le_one"], "deps": ["affinecurvepoint"], "status": "done", "x": 278, "y": 17300, "paper": "projective"});
nodes.push({"id": "completecurveclosure", "title": "实际曲线的完整闭包", "statement": "完整环境中的一维整曲线 immersion，其实际 Scheme 像闭包仍整、完整且维数为 1。", "scope": "实际像的约化、不可约、函数域嵌入和开浸入均由几何证明；不假定闭包是曲线。", "inputs": ["实际像的约化、不可约、函数域嵌入和开浸入均由几何证明；不假定闭包是曲线。"], "steps": [["实际曲线的完整闭包", "实际像的约化、不可约、函数域嵌入和开浸入均由几何证明；不假定闭包是曲线。", "complete_integral_curve_actual_closure"]], "file": "CompleteCurveClosure.lean", "decl": "complete_integral_curve_actual_closure", "related": ["dominant_functionField_constants_comp", "quasiCompact_integral_actual_image_isIntegral"], "deps": ["functionfielddimension", "curveimagecases"], "status": "done", "x": 278, "y": 17450, "paper": "projective"});
nodes.push({"id": "completecurvepoint", "title": "完整整簇：曲线通过指定闭点", "statement": "完整整簇中的非泛闭点位于一条实际闭嵌入的完整整曲线上。", "scope": "先在真实仿射图构造一维素理想商，再取实际闭包，保留指定闭点。曲线及维数、完整性、闭嵌入全部构造。", "inputs": ["先在真实仿射图构造一维素理想商，再取实际闭包，保留指定闭点。曲线及维数、完整性、闭嵌入全部构造。"], "steps": [["完整整簇：曲线通过指定闭点", "先在真实仿射图构造一维素理想商，再取实际闭包，保留指定闭点。曲线及维数、完整性、闭嵌入全部构造。", "exists_complete_integral_curve_through_closed_point"]], "file": "CompleteCurveThroughPoint.lean", "decl": "exists_complete_integral_curve_through_closed_point", "related": ["affine_chart_not_field_at_nonGeneric_point", "dimension_one_of_curve_domain"], "deps": ["affinecurvepoint", "completecurveclosure"], "status": "done", "x": 278, "y": 17600, "paper": "projective"});
nodes.push({"id": "integralclosedsubscheme", "title": "闭不可约集合的实际整子概形", "statement": "闭不可约集合的消失理想子概形实际约化、不可约，闭嵌入的像恰为该集合。", "scope": "在每个仿射图验证 radical 商环约化，再沿实际开覆盖粘接；约化子概形不是额外假设。", "inputs": ["在每个仿射图验证 radical 商环约化，再沿实际开覆盖粘接；约化子概形不是额外假设。"], "steps": [["闭不可约集合的实际整子概形", "在每个仿射图验证 radical 商环约化，再沿实际开覆盖粘接；约化子概形不是额外假设。", "closed_irreducible_actual_subscheme_properties"]], "file": "IntegralClosedSubscheme.lean", "decl": "closed_irreducible_actual_subscheme_properties", "related": ["vanishingIdeal_subscheme_isReduced"], "deps": [], "status": "done", "x": 278, "y": 17750, "paper": "projective"});
nodes.push({"id": "nonisolatedcurve", "title": "完整纤维：非孤立闭点上的曲线", "statement": "完整 Scheme 中的非孤立闭点位于一条实际完整整曲线上，纤维本身可以可约或非约化。", "scope": "Noetherian 不可约分量的有限性给含该点的正维分量；取实际约化整子概形并应用闭点曲线定理。", "inputs": ["Noetherian 不可约分量的有限性给含该点的正维分量；取实际约化整子概形并应用闭点曲线定理。"], "steps": [["完整纤维：非孤立闭点上的曲线", "Noetherian 不可约分量的有限性给含该点的正维分量；取实际约化整子概形并应用闭点曲线定理。", "exists_complete_integral_curve_through_nonisolated_closed_point"]], "file": "NonisolatedCompleteCurve.lean", "decl": "exists_complete_integral_curve_through_nonisolated_closed_point", "related": ["nonisolated_point_positive_irreducible_component"], "deps": ["completecurvepoint", "integralclosedsubscheme"], "status": "done", "x": 278, "y": 17900, "paper": "projective"});
Object.assign(find('cover'),{"title": "exceptional 闭点的实际完整曲线", "statement": "每个 exceptional 闭点都位于一条实际被 f 压缩的完整整曲线上。", "scope": "正规底上的实际 proper birational 态射。对每个 exceptional 闭点，Zariski 主定理排除孤立纤维点；在实际纤维内构造完整整曲线，再闭嵌入原环境。任意特征代数闭域；没有曲线存在性 input。", "status": "done", "file": "ExceptionalCompleteCurve.lean", "decl": "exceptional_closed_point_complete_contracted_curve", "related": [], "deps": ["zmtpoint", "nonisolatedcurve"], "inputs": ["任意特征代数闭域；整 X、Y，Y 局部有限型且所有 stalk 整闭。", "f 是实际 proper birational 态射；x 为闭点。", "f(x) 的任何开邻域上，f 都不是同构；这是实际 center 的定义条件。"], "steps": [["实际纤维非孤立", "Zariski 主定理排除 exceptional 纤维中的孤立点。", "exceptional_fiber_point_not_isOpen_singleton"], ["完整整曲线：已构造", "正规底上的实际 proper birational 态射。对每个 exceptional 闭点，Zariski 主定理排除孤立纤维点；在实际纤维内构造完整整曲线，再闭嵌入原环境。任意特征代数闭域；没有曲线存在性 input。", "exceptional_closed_point_complete_contracted_curve"]]});
Object.assign(find('curves'),{"title": "归零 exceptional 素系数：实际压缩曲线", "statement": "B 有效且 exceptional 素点 η 的系数为零，则构造完整压缩整曲线 C，使 C 不被 Supp B 包含且 B·C≥0。", "scope": "有效实际 R-Cartier 的归零素系数说明该素点不在实际 Weil 支撑闭包中。实际构造支撑外闭点，并用 exceptional 曲线覆盖构造经过它的压缩曲线；该曲线不被支撑包含，真实正规化交数非负。此步不需要整条曲线位于 F 中，也不依赖第二部分的连通纤维。", "status": "done", "file": "ZeroPrimeCurve.lean", "decl": "zero_exceptional_prime_actual_curve_nonnegative_intersection", "related": ["zero_weil_coefficient_outside_geometric_support"], "deps": ["cover", "closedpoint", "normalizedsigns"], "inputs": ["X、Y 整且正规，X 紧且局部 Noetherian；f proper birational，Y 局部有限型于任意特征代数闭域。", "B 为真实有限 Cartier 家族的任意实线性组合，实际所有 Weil 系数非负。", "η 为余维一素点，实际 B 系数为零；f(η) 属于实际 center。", "这是给定归零 exceptional 素点后的几何步骤。D 不有效如何从 f_*D 有效推到这一条件，仍由主证明另行处理。"], "steps": [["零系数与支撑", "有限 Weil 支撑的余维一分量不可能严格特化为另一余维一点，故 η 不在支撑闭包。", "zero_weil_coefficient_outside_geometric_support"], ["闭点与实际压缩曲线", "选 x∈闭包{η}∖Supp B；center 条件随特化传递。实际构造经过 x 的完整压缩曲线。", "exceptional_closed_point_complete_contracted_curve"], ["真实交数非负", "有效实际 R-Cartier 的归零素系数说明该素点不在实际 Weil 支撑闭包中。实际构造支撑外闭点，并用 exceptional 曲线覆盖构造经过它的压缩曲线；该曲线不被支撑包含，真实正规化交数非负。此步不需要整条曲线位于 F 中，也不依赖第二部分的连通纤维。", "zero_exceptional_prime_actual_curve_nonnegative_intersection"]]});
find('connected').inputs[3]='已完成：每个 exceptional 闭点的实际完整压缩曲线覆盖。仍需修补同时遇支撑却不被包含的高维相交曲线选择；覆盖不等于这个更强结论。';
find('connected').steps[3]=['高维相交曲线：待修补','完整压缩曲线覆盖已完成；还需证明曲线可以同时遇支撑且不包含于支撑。这一步只属于第二部分。'];

// Actual geometric negativity with explicit anti-ample witness, formal-31
nodes.push({"id": "actualnegativecenter", "title": "真实负系数必在 exceptional center", "statement": "实际 cycle 的推出有效，则每个负系数的像都不属于任何同构开集。", "scope": "在任何实际同构开集上，唯一原像的余维一致、stalk 同构、剩余域次数为 1，故真实 cycle 推出系数等于原系数。推出有效时，负系数不可能在该开集上。因此每个负系数像都属于实际 center；没有 strict 系数模型或 exceptional 识别 input。", "status": "done", "file": "NegativeActualCenter.lean", "decl": "actual_negative_coefficient_image_in_center", "related": ["actual_cycle_coefficient_over_isomorphism_open"], "deps": ["geomcycle", "localorder"], "inputs": ["实际 quasi-compact Scheme 态射，真实实系数 cycle。", "AlgebraicCycle.map 使用实际 Order.coheight 权重，推出的实际系数逐点非负。"], "steps": [["同构开集上的实际系数", "真实唯一原像、余维一致及剩余域次数 1 给系数保留。", "actual_cycle_coefficient_over_isomorphism_open"], ["负系数识别为 center", "在任何实际同构开集上，唯一原像的余维一致、stalk 同构、剩余域次数为 1，故真实 cycle 推出系数等于原系数。推出有效时，负系数不可能在该开集上。因此每个负系数像都属于实际 center；没有 strict 系数模型或 exceptional 识别 input。", "actual_negative_coefficient_image_in_center"]], "x": 278, "y": 18150, "paper": "projective"});
Object.assign(find('core'),{"title": "实际几何 negativity：尚需 E 见证", "statement": "实际 f_*D 有效且 −D 为 f-nef，给定有效、覆盖 exceptional 素点且交数严格负的实际 E，则 D 实际有效。", "scope": "第一部分的实际几何反证法已通过：真实 Cartier 支撑有限性给有限系数向量；实际推出有效性识别负素点为 center；最大比值产生归零点；实际压缩曲线及实际交数非负定理完成矛盾。仍明确假设同一个 E 有效、覆盖 exceptional 素点，且在所有实际压缩闭嵌入曲线上交数严格负。没有 hcurve、任意给定交数映射或 center 识别 input；E 的构造和几何 ample 正性尚未完成，所以仍是条件式证明。", "status": "conditional", "file": "ActualNegativityWitness.lean", "decl": "actual_negativity_of_antiample_witness", "related": ["actualRealCartierCoefficients_apply"], "deps": ["max", "actualnegativecenter", "curves", "antiample", "intersection", "nefpull"], "inputs": ["任意特征代数闭域；正规整 X、Y，X 紧，f proper birational，Y 局部有限型。", "D、E 由同一个实际有限 Cartier 家族及任意实权重表示；f_*D 实际有效，−D 按实际压缩完整曲线定义为 f-nef。", "剩余 E 见证：E 实际有效，且每个 actual center 上的素点有正 E 系数。", "剩余 E 见证：每条实际完整压缩闭嵌入整曲线上 E·C<0。几何 −E f-ample 导出此条件仍待证明。"], "steps": [["真实系数与 center", "从实际支撑有限性构造 Finsupp，并从真实推出有效性证明负系数属于 center。", "actual_negative_coefficient_image_in_center"], ["实际最大比值", "取得 e>0，B=D+eE 有效，在一个负素点归零。", "exists_effective_shift"], ["实际曲线与交数", "支撑外闭点、实际压缩曲线以及 B·C≥0 全部由几何定理构造。", "zero_exceptional_prime_actual_curve_nonnegative_intersection"], ["条件式反证法完成", "−D f-nef 给 D·C≤0；E 见证给 E·C<0；由真实线性交数得到矛盾。", "actual_negativity_of_antiample_witness"]]});
find('curves').deps.push('actualnegativecenter');
find('curves').inputs[3]='已完成：从真实 f_*D 有效性证明负系数的像属于实际 center。主证明仍需 E 的覆盖和严格负交数见证。';

// Actual high-dimensional crossing curves and support dichotomy, formal-32
nodes.push({"id": "affinelineavoid", "title": "过指定点的仿射直线：支撑避让", "statement": "非零多项式的指定零点处，实际构造经过该点但不包含于零集的直线。", "scope": "无限域上的多项式求值选出方向；显式限制映射满射，实际素理想核避开该多项式。", "inputs": ["无限域上的多项式求值选出方向；显式限制映射满射，实际素理想核避开该多项式。"], "steps": [["过指定点的仿射直线：支撑避让", "无限域上的多项式求值选出方向；显式限制映射满射，实际素理想核避开该多项式。", "affine_line_through_point_avoiding_polynomial"]], "file": "AffineLineAvoiding.lean", "decl": "affine_line_through_point_avoiding_polynomial", "related": [], "deps": ["affinelinepoint"], "status": "done", "x": 278, "y": 18300, "paper": "fiber"});
nodes.push({"id": "affinecurveavoid", "title": "仿射整曲线：同时过点并避让", "statement": "非零函数 v 在指定闭点消失时，实际构造一维素理想 P⊂m，且 v∉P。", "scope": "Noether 正规化中，积分关系给 (v) 内非零基环元素；选避开它的直线，再 going-down。不假设曲线或避让条件。", "inputs": ["Noether 正规化中，积分关系给 (v) 内非零基环元素；选避开它的直线，再 going-down。不假设曲线或避让条件。"], "steps": [["仿射整曲线：同时过点并避让", "Noether 正规化中，积分关系给 (v) 内非零基环元素；选避开它的直线，再 going-down。不假设曲线或避让条件。", "affine_integral_curve_through_maximal_avoiding"]], "file": "AffineCurveAvoiding.lean", "decl": "affine_integral_curve_through_maximal_avoiding", "related": [], "deps": ["affinelineavoid", "affinecurvepoint"], "status": "done", "x": 278, "y": 18450, "paper": "fiber"});
nodes.push({"id": "completecurveavoid", "title": "完整整簇：支撑点上的避让曲线", "statement": "任意非空真闭子集内的指定闭点，位于一条实际完整整曲线上，该曲线不包含于闭子集。", "scope": "实际仿射零集提供非零消失函数；构造避让曲线并取真实 Scheme 闭包。保留指定点和非包含性。", "inputs": ["实际仿射零集提供非零消失函数；构造避让曲线并取真实 Scheme 闭包。保留指定点和非包含性。"], "steps": [["完整整簇：支撑点上的避让曲线", "实际仿射零集提供非零消失函数；构造避让曲线并取真实 Scheme 闭包。保留指定点和非包含性。", "exists_complete_integral_curve_through_closed_point_avoiding"]], "file": "CompleteCurveAvoiding.lean", "decl": "exists_complete_integral_curve_through_closed_point_avoiding", "related": [], "deps": ["affinecurveavoid", "completecurveclosure"], "status": "done", "x": 278, "y": 18600, "paper": "fiber"});
nodes.push({"id": "connectedcrossing", "title": "高维连通完整 Scheme：实际相交曲线", "statement": "连通完整 Scheme 的任意非空真闭子集，被一条实际完整整曲线遇到而不包含该曲线。", "scope": "概形可约、非约化，维数任意。有限不可约分量和连通性给跨越分量，取其实际约化整子概形，再构造曲线。连通性是定理假设，不假设曲线存在。", "inputs": ["概形可约、非约化，维数任意。有限不可约分量和连通性给跨越分量，取其实际约化整子概形，再构造曲线。连通性是定理假设，不假设曲线存在。"], "steps": [["高维连通完整 Scheme：实际相交曲线", "概形可约、非约化，维数任意。有限不可约分量和连通性给跨越分量，取其实际约化整子概形，再构造曲线。连通性是定理假设，不假设曲线存在。", "connected_complete_scheme_actual_crossing_curve"]], "file": "ConnectedCurveCrossing.lean", "decl": "connected_complete_scheme_actual_crossing_curve", "related": ["connected_closed_subset_crossing_component"], "deps": ["completecurveavoid", "integralclosedsubscheme", "closedpoint"], "status": "done", "x": 278, "y": 18750, "paper": "fiber"});
Object.assign(find('fiber'),{"title": "实际连通压缩 Scheme 的支撑二择一", "statement": "D 实际有效，−D 为 f-nef：连通完整压缩 Scheme 与 Supp D 不相交或全在其中。应用于所有纤维仍需证明纤维连通性。", "scope": "实际有效 R-Cartier 除子，−D 在真实压缩完整曲线上 nef。对任意实际连通、完整、被 f 压缩的 Scheme Z→X，已证明它与实际 Supp D 不相交或全在其中。高维相交曲线与交数严格正性均已证明，Z 可约或非约化。把此结果应用到所有 actual proper birational 纤维，仍需独立证明这些纤维连通及对应的底域接口；不能据此把全局纤维连通性标为完成。", "status": "conditional", "file": "ActualConnectedSupport.lean", "decl": "actual_connected_contracted_scheme_support_dichotomy", "related": [], "deps": ["connectedcrossing", "normalizedsigns", "nefpull", "connected"], "inputs": ["任意特征代数闭域；X 正规、整、紧且局部 Noetherian。", "实际 Cartier 有限家族的实组合有效；−D 是真实压缩完整曲线上的相对 nef。", "Z→X 复合到底域 proper，复合 f 为常值；Z 连通是本定理的明确假设。", "剩余应用输入：从正规底上的 proper birational 几何证明全部实际纤维连通，以及一般纤维底域转换。"], "steps": [["反设部分遇支撑", "实际拉回闭集 T 非空且为真闭集。"], ["实际高维相交曲线：已完成", "从 Z 的连通性构造完整整曲线，遇到 T 且不被包含。", "connected_complete_scheme_actual_crossing_curve"], ["真实正交数与 nef 矛盾", "实际交数严格正，而 −D f-nef 给交数非正。得到支撑二择一。", "actual_connected_contracted_scheme_support_dichotomy"]]});
find('connected').title='proper 双有理实际纤维的连通性';
find('connected').statement='剩余需要证明：正规底上的 proper birational 态射，其实际纤维连通。高维相交曲线选择已完成。';
find('connected').scope='Hartshorne III §11 路线的正规性、形式函数与幂等元证明仍需实际层论桥接；最后局部环矛盾已验证。高维相交曲线已由 connectedcrossing 在任意维数、可约与非约化完整 Scheme 上证明，不再是曲线选择缺口。此节点只保留实际纤维连通性。';
find('connected').deps=['normalfinite','localidempotents'];
find('connected').inputs[3]='已完成：对任何实际连通完整 Scheme 构造遇支撑而不被包含的完整整曲线。仍缺 proper birational 的实际纤维连通性。';
find('connected').steps[3]=['高维相交曲线：已完成','可约、非约化的实际连通完整 Scheme 上，遇真闭子集而不被包含的完整整曲线已经构造。','connected_complete_scheme_actual_crossing_curve'];
find('chow').scope=find('chow').scope.replace('独立的高维曲线选择与连通性证明','独立的实际纤维连通性证明；高维相交曲线选择已完成');

nodes.push({"id": "effectivetwist", "title": "仿射底清分母：构造有效 Cartier 代表", "statement": "任意实际 Cartier 除子，在仿射双有理底上可构造有效主除子移动。", "scope": "紧性取有限真实仿射覆盖。双有理函数域同构将方程送回底环分式域，取共同非零分母；实际 stalk 拉回与单位过渡证明所有局部方程正规。没有截面存在或有效性 input。", "inputs": ["紧性取有限真实仿射覆盖。双有理函数域同构将方程送回底环分式域，取共同非零分母；实际 stalk 拉回与单位过渡证明所有局部方程正规。没有截面存在或有效性 input。"], "steps": [["仿射底清分母：构造有效 Cartier 代表", "紧性取有限真实仿射覆盖。双有理函数域同构将方程送回底环分式域，取共同非零分母；实际 stalk 拉回与单位过渡证明所有局部方程正规。没有截面存在或有效性 input。", "exists_effective_cartier_rational_twist"]], "file": "CartierEffectiveTwist.lean", "decl": "exists_effective_cartier_rational_twist", "related": [], "deps": ["normalizationbirational", "cartiercurve"], "status": "done", "x": 278, "y": 19000, "paper": "antiample"});

nodes.push({"id": "normalizedprincipal", "title": "任意完整整曲线：环境主除子移动不变", "statement": "对任意实际有理函数主除子移动，真实正规化交数不变。", "scope": "原曲线可非正规，且可包含于主函数的支撑。构造实际有限正规化，比较合法 Cartier 限制，不直接对不能拉回的函数强行限制。", "inputs": ["原曲线可非正规，且可包含于主函数的支撑。构造实际有限正规化，比较合法 Cartier 限制，不直接对不能拉回的函数强行限制。"], "steps": [["任意完整整曲线：环境主除子移动不变", "原曲线可非正规，且可包含于主函数的支撑。构造实际有限正规化，比较合法 Cartier 限制，不直接对不能拉回的函数强行限制。", "complete_integral_curve_ambient_cartier_principal_invariance"]], "file": "NormalizedPrincipalInvariance.lean", "decl": "complete_integral_curve_ambient_cartier_principal_invariance", "related": [], "deps": ["curvenormalization", "ambientmoving"], "status": "done", "x": 278, "y": 19150, "paper": "antiample"});

nodes.push({"id": "effectiveexceptional", "title": "有效 E 与 exceptional 正系数：已构造", "statement": "给定实际严格负的 Cartier 除子，构造有效 E，并证明每个 exceptional 素点的 E 系数严格正。", "scope": "E 的有效性和 exceptional 覆盖均为输出。若某 exceptional 素点系数零，已构造的实际压缩曲线给 E·C≥0，而主除子不变及严格负次数给矛盾。几何射影性到 O(1) 截面覆盖仍待构造。", "inputs": ["E 的有效性和 exceptional 覆盖均为输出。若某 exceptional 素点系数零，已构造的实际压缩曲线给 E·C≥0，而主除子不变及严格负次数给矛盾。几何射影性到 O(1) 截面覆盖仍待构造。"], "steps": [["有效 E 与 exceptional 正系数：已构造", "E 的有效性和 exceptional 覆盖均为输出。若某 exceptional 素点系数零，已构造的实际压缩曲线给 E·C≥0，而主除子不变及严格负次数给矛盾。几何射影性到 O(1) 截面覆盖仍待构造。", "exists_effective_exceptional_covering_cartier_twist"]], "file": "EffectiveExceptionalWitness.lean", "decl": "exists_effective_exceptional_covering_cartier_twist", "related": [], "deps": ["effectivetwist", "normalizedprincipal", "curves", "affinesectionpositive", "cartierinverse", "projectivesections"], "status": "conditional", "x": 278, "y": 19300, "paper": "antiample"});

nodes.push({"id": "completeaffineavoid", "title": "完整曲线必遇仿射开集的补集", "statement": "实际闭嵌入的完整整曲线不能全包含于环境仿射开集。", "scope": "否则闭因子分解使完整曲线仿射。proper 整概形的全局函数环为域，因而仿射维数零，与曲线的一维矛盾。", "inputs": ["否则闭因子分解使完整曲线仿射。proper 整概形的全局函数环为域，因而仿射维数零，与曲线的一维矛盾。"], "steps": [["完整曲线必遇仿射开集的补集", "否则闭因子分解使完整曲线仿射。proper 整概形的全局函数环为域，因而仿射维数零，与曲线的一维矛盾。", "complete_integral_curve_meets_complement_affine_open"]], "file": "CompleteCurveAffineAvoidance.lean", "decl": "complete_integral_curve_meets_complement_affine_open", "related": ["complete_integral_curve_not_affine"], "deps": ["curveparameter"], "status": "done", "x": 278, "y": 19450, "paper": "antiample"});

nodes.push({"id": "normalizedcartiersigns", "title": "实际 Cartier 有效性与正交数", "statement": "有效 Cartier 除子与任意完整整曲线交数非负；遇支撑而不被包含则严格正。", "scope": "实际有限正规化搬运泛点避让及支撑相交，包含奇异、非正规完整整曲线。", "inputs": ["实际有限正规化搬运泛点避让及支撑相交，包含奇异、非正规完整整曲线。"], "steps": [["实际 Cartier 有效性与正交数", "实际有限正规化搬运泛点避让及支撑相交，包含奇异、非正规完整整曲线。", "complete_integral_curve_effective_cartier_intersection_signs"]], "file": "NormalizedCartierSigns.lean", "decl": "complete_integral_curve_effective_cartier_intersection_signs", "related": [], "deps": ["curvenormalization", "effectiveintersection"], "status": "done", "x": 278, "y": 19600, "paper": "antiample"});

nodes.push({"id": "affinesectionpositive", "title": "仿射截面覆盖 ⇒ 实际正次数", "statement": "实际有效线性等价除子的仿射非零集覆盖，推出所有闭嵌入完整整曲线的真实 Cartier 交数严格正。", "scope": "假设仅为实际截面及其仿射非零集的几何覆盖，没有正次数条件。选一个泛点不消失的截面；完整曲线必遇其零除子，由实际有效正性及主移动不变得到原除子的正次数。从射影嵌入构造这些数据是单独的未完成节点。", "inputs": ["假设仅为实际截面及其仿射非零集的几何覆盖，没有正次数条件。选一个泛点不消失的截面；完整曲线必遇其零除子，由实际有效正性及主移动不变得到原除子的正次数。从射影嵌入构造这些数据是单独的未完成节点。"], "steps": [["仿射截面覆盖 ⇒ 实际正次数", "假设仅为实际截面及其仿射非零集的几何覆盖，没有正次数条件。选一个泛点不消失的截面；完整曲线必遇其零除子，由实际有效正性及主移动不变得到原除子的正次数。从射影嵌入构造这些数据是单独的未完成节点。", "complete_integral_curve_positive_of_affine_section_cover"]], "file": "CartierAffineSections.lean", "decl": "complete_integral_curve_positive_of_affine_section_cover", "related": [], "deps": ["completeaffineavoid", "normalizedcartiersigns", "normalizedprincipal"], "status": "done", "x": 278, "y": 19750, "paper": "antiample"});

nodes.push({"id": "cartierinverse", "title": "实际 Cartier 负号与交数负号", "statement": "反转真实局部方程与 stalk 单位，构造 −A，并证明 (−A)·C=−(A·C)。", "scope": "实际 DVR 阶数给相反系数；已证明的实 Cartier 表示独立性推出任意完整整曲线上的交数负号。", "inputs": ["实际 DVR 阶数给相反系数；已证明的实 Cartier 表示独立性推出任意完整整曲线上的交数负号。"], "steps": [["实际 Cartier 负号与交数负号", "实际 DVR 阶数给相反系数；已证明的实 Cartier 表示独立性推出任意完整整曲线上的交数负号。", "complete_integral_curve_cartier_intersection_inverse"]], "file": "CartierInverse.lean", "decl": "complete_integral_curve_cartier_intersection_inverse", "related": ["cartierAtlas_inverse_coefficient"], "deps": ["realpresentation", "normalizedintersection"], "status": "done", "x": 278, "y": 19900, "paper": "antiample"});
nodes.push({"id": "projectivesections", "title": "相对 O(1)：实际 Cartier 截面覆盖", "statement": "待构造：从实际相对射影闭嵌入得到 O(1) 的 Cartier 方程与坐标截面，其仿射非零集覆盖 X。", "scope": "定义性几何路线：在标准射影坐标开集上取齐次坐标之比，构造真实 Cartier 局部方程、单位过渡、有效坐标截面及其仿射非零集。清分母、E 有效性、exceptional 覆盖和正交数均已另行完成。此节点只保留射影闭嵌入到实际截面数据的构造。", "inputs": ["实际闭嵌入 i:X→P^n_R，仿射底 Spec R。", "在非空标准坐标开集上构造 O(1) 的齐次比方程；证明实际 stalk 单位过渡。", "构造实际有效坐标截面，识别其非零集为仿射开集并证明覆盖。"], "steps": [["齐次比的实际 Cartier 方程", "选择一个泛点不消失的坐标，在各非空标准开集上构造其与分母坐标的比。"], ["坐标截面与仿射非零集", "证明 stalk 过渡、有效性和零集；由标准坐标开集的仿射性及闭嵌入得到实际覆盖。"]], "deps": ["localcartier"], "status": "assumption", "x": 20, "y": 19900, "paper": "antiample"});
Object.assign(find('antiample'),{"title": "E 构造已完成：尚需射影坐标数据", "statement": "清分母构造有效 E，主移动保持真实交数，exceptional 素点的 E 系数严格正均已证明。剩余是 O(1) 的实际截面数据。", "scope": "原先的非零直接像截面路线已用实际仿射底清分母替代，不再需要直接像拟凝聚或非零性的 input。E 的有效性与 exceptional 覆盖已构造；O(1) 的仿射截面覆盖给出正次数的证明也已完成。相对射影闭嵌入到这些实际 Cartier 截面数据仍需构造，所以此应用节点保持条件式。", "status": "conditional", "file": "EffectiveExceptionalWitness.lean", "decl": "exists_effective_exceptional_covering_cartier_twist", "related": [], "deps": ["effectivetwist", "effectiveexceptional", "affinesectionpositive", "cartierinverse", "projectivesections"], "inputs": ["已完成：实际仿射底清分母，从任意 Cartier 方程构造有效主移动。", "已完成：任意完整整曲线上的实际主移动不变、E 覆盖 exceptional 素点。", "已完成：实际仿射非零截面覆盖给正次数，不假设交数正性。", "待完成：从实际相对射影闭嵌入构造 O(1) 的 Cartier 截面覆盖。"], "steps": [["仿射底清分母：已完成", "从有限实际 Cartier 图册构造非零共同底环分母，主移动后有效。", "exists_effective_cartier_rational_twist"], ["实际正次数：已完成", "仿射非零截面覆盖推出完整曲线正次数，再取负 Cartier 除子。", "complete_integral_curve_positive_of_affine_section_cover"], ["E exceptional 覆盖：已完成", "零系数的实际压缩曲线与严格负次数矛盾。", "exists_effective_exceptional_covering_cartier_twist"], ["剩余射影坐标构造", "从 O(1) 的齐次比局部方程构造实际覆盖数据。"]]});
Object.assign(find('intersection'),{"title": "几何截面正次数：已证明条件", "statement": "相对 nef 按真实压缩完整曲线定义。实际仿射非零截面覆盖已推出 Cartier 正交数；剩余为射影坐标数据的构造。", "scope": "实际 Cartier/R-Cartier 交数、正规化、有效性符号与支撑正性均已完成。新的几何证明从实际有效线性等价除子的仿射非零集覆盖出发，推出所有实际闭嵌入完整整曲线的严格正交数，没有给定正次数 input。标准相对 O(1) 提供此数据的实际 Lean 构造仍在 projectivesections 节点。", "status": "conditional", "file": "CartierAffineSections.lean", "decl": "complete_integral_curve_positive_of_affine_section_cover", "related": [], "deps": ["nefpull", "affinesectionpositive", "cartierinverse", "projectivesections"], "inputs": ["已完成：真实完整整曲线交数及相对 nef 符号。", "已完成：实际仿射非零截面覆盖 ⇒ 实际正次数。", "待完成：实际射影坐标截面满足该几何覆盖。"], "steps": [["相对 nef 定义", "仅测试被 f 压缩的实际完整曲线，−D f-nef 给 D·C≤0。", "actual_relative_nef_negative_iff"], ["仿射几何正性：已完成", "完整曲线必遇有效坐标零除子，主移动不变给原 Cartier 除子正次数。", "complete_integral_curve_positive_of_affine_section_cover"], ["尚需 O(1) 坐标数据", "接入实际齐次比方程及标准坐标开集覆盖。"]]});
Object.assign(find('core'),{"title": "实际 negativity：只需几何截面覆盖", "statement": "实际 f_*D 有效且 −D 为 f-nef；给定实际 Cartier 的仿射非零截面覆盖，推出 D 实际有效。E 和交数正性均在证明中构造。", "scope": "第一部分已从实际几何截面覆盖接通：仿射非零集给正次数，取负 Cartier 除子、清分母构造有效 E，证明 exceptional 素系数严格正，再执行最大比值、实际压缩曲线与真实交数的反证。没有 E 有效性、E 覆盖、数值正性、给定交数映射或曲线存在 input。仍明确要求实际 Cartier 仿射截面覆盖；从相对射影闭嵌入构造 O(1) 的这个数据尚未完成，完整主定理仍待形式化。", "status": "conditional", "file": "ActualNegativityAffineSections.lean", "decl": "actual_negativity_of_affine_section_cover", "related": ["actual_negativity_of_strictly_negative_cartier", "actual_negativity_of_antiample_witness"], "deps": ["max", "actualnegativecenter", "curves", "antiample", "intersection", "projectivesections"], "inputs": ["任意特征代数闭域；正规整 X、Y，仿射 Y，X 紧，f proper birational，Y 局部有限型。", "实际有限 Cartier 家族与任意实权重表示 D；实际 f_*D 有效，−D 相对 nef。", "唯一新增几何输入：实际 Cartier 除子的有效线性等价截面，其仿射非零集覆盖 X。", "剩余：从相对射影闭嵌入构造 O(1) 的上述实际数据；完整主定理没有因此标为完成。"], "steps": [["几何正次数", "实际仿射截面非零集覆盖 ⇒ 完整曲线正次数。", "complete_integral_curve_positive_of_affine_section_cover"], ["有效 E 与覆盖", "清分母构造有效 E，并用真实压缩曲线证明 exceptional 系数正。", "exists_effective_exceptional_covering_cartier_twist"], ["最大比值与实际反证", "实际负系数识别、归零系数、压缩曲线与真实交数给矛盾。", "actual_negativity_of_strictly_negative_cartier"], ["条件式实际几何定理", "正次数、E 的有效性及覆盖均已导出。仍需构造 O(1) 的实际几何截面覆盖。", "actual_negativity_of_affine_section_cover"]]});

nodes.push({"id": "projratios", "title": "实际 Proj 齐次比与 stalk 单位", "statement": "同次数齐次坐标之比给实际 Proj stalk 元素；单位当且仅当分子坐标不消失。", "scope": "使用 mathlib 的真实齐次局部化及 Proj stalk 同构，证明乘法恒等式与实际坐标截面的 germ。没有形式符号或单位判据 input。", "inputs": ["使用 mathlib 的真实齐次局部化及 Proj stalk 同构，证明乘法恒等式与实际坐标截面的 germ。没有形式符号或单位判据 input。"], "steps": [["实际 Proj 齐次比与 stalk 单位", "使用 mathlib 的真实齐次局部化及 Proj stalk 同构，证明乘法恒等式与实际坐标截面的 germ。没有形式符号或单位判据 input。", "proj_coordinate_ratio_section_germ"]], "file": "ProjCoordinateRatios.lean", "decl": "proj_coordinate_ratio_section_germ", "related": ["proj_coordinate_ratio_stalk_unit_iff", "proj_coordinate_ratio_stalk_mul"], "deps": ["localcartier"], "status": "done", "x": 278, "y": 20100, "paper": "antiample"});

nodes.push({"id": "projpullback", "title": "齐次比拉回：实际有理函数", "statement": "坐标比截面拉回整概形，并送入实际函数域；证明局部兼容、非零性和比值乘法。", "scope": "不假定闭嵌入为 dominant。泛点处坐标非零给实际截面 germ 为单位，截面到函数域的单射证明比值非零。", "inputs": ["不假定闭嵌入为 dominant。泛点处坐标非零给实际截面 germ 为单位，截面到函数域的单射证明比值非零。"], "steps": [["齐次比拉回：实际有理函数", "不假定闭嵌入为 dominant。泛点处坐标非零给实际截面 germ 为单位，截面到函数域的单射证明比值非零。", "pulled_proj_coordinate_ratio_mul"]], "file": "ProjCoordinatePullback.lean", "decl": "pulled_proj_coordinate_ratio_mul", "related": ["pulled_proj_coordinate_ratio_local", "pulled_proj_coordinate_ratio_ne_zero"], "deps": ["projratios", "cartiercurve"], "status": "done", "x": 278, "y": 20250, "paper": "antiample"});

nodes.push({"id": "projcartier", "title": "射影坐标构造实际 Cartier 图册", "statement": "实际 Proj 闭嵌入上，选择泛点坐标，构造齐次比方程与实际 stalk 单位过渡。", "scope": "非空标准坐标开集的闭嵌入拉回为实际仿射图册。过渡由 Proj stalk 比值单位与实际拉回乘法证明，没有 Cartier 图册 input。", "inputs": ["非空标准坐标开集的闭嵌入拉回为实际仿射图册。过渡由 Proj stalk 比值单位与实际拉回乘法证明，没有 Cartier 图册 input。"], "steps": [["射影坐标构造实际 Cartier 图册", "非空标准坐标开集的闭嵌入拉回为实际仿射图册。过渡由 Proj stalk 比值单位与实际拉回乘法证明，没有 Cartier 图册 input。", "exists_actual_proj_cartier_atlas"]], "file": "ProjCartierAtlas.lean", "decl": "exists_actual_proj_cartier_atlas", "related": ["proj_coordinate_generic_of_point"], "deps": ["projpullback"], "status": "done", "x": 278, "y": 20400, "paper": "antiample"});

nodes.push({"id": "projcoordsections", "title": "坐标零集与仿射非零截面覆盖", "statement": "构造实际有效坐标截面，并证明其支撑补集等于标准坐标开集的拉回。", "scope": "有效性由真实 stalk 正规方程给出；单位判据识别精确支撑。坐标非零集仿射且覆盖，从而构造 CartierAffineSectionCover，而非把它作为假设。", "inputs": ["有效性由真实 stalk 正规方程给出；单位判据识别精确支撑。坐标非零集仿射且覆盖，从而构造 CartierAffineSectionCover，而非把它作为假设。"], "steps": [["坐标零集与仿射非零截面覆盖", "有效性由真实 stalk 正规方程给出；单位判据识别精确支撑。坐标非零集仿射且覆盖，从而构造 CartierAffineSectionCover，而非把它作为假设。", "exists_actual_proj_cartier_affine_section_cover"]], "file": "ProjCartierSections.lean", "decl": "exists_actual_proj_cartier_affine_section_cover", "related": [], "deps": ["projcartier", "cartiersupport"], "status": "done", "x": 278, "y": 20550, "paper": "antiample"});

nodes.push({"id": "projgenerators", "title": "同次齐次生成元自动给出覆盖", "statement": "正次数齐次生成元覆盖实际 Proj；从实际点选择坐标，构造 Cartier 截面数据。", "scope": "使用实际 irrelevant ideal 与 Proj 标准开集覆盖定理。标准多项式变量确实生成次数零子环上的整个环，另由多项式归纳证明。", "inputs": ["使用实际 irrelevant ideal 与 Proj 标准开集覆盖定理。标准多项式变量确实生成次数零子环上的整个环，另由多项式归纳证明。"], "steps": [["同次齐次生成元自动给出覆盖", "使用实际 irrelevant ideal 与 Proj 标准开集覆盖定理。标准多项式变量确实生成次数零子环上的整个环，另由多项式归纳证明。", "exists_actual_proj_sections_of_generators"]], "file": "ProjStandardSections.lean", "decl": "exists_actual_proj_sections_of_generators", "related": [], "deps": ["projcoordsections"], "status": "done", "x": 278, "y": 20700, "paper": "antiample"});
Object.assign(find('projectivesections'),{"title": "相对射影空间：实际 O(1) 数据已构造", "statement": "从实际标准射影空间闭嵌入，构造 Cartier 除子、有效坐标截面及覆盖 X 的仿射非零集。", "scope": "所有坐标几何数据都是输出。标准变量生成次数零子环上的多项式环；实际 Proj 标准开集覆盖、齐次比 stalk 单位和截面 germ 构造图册，真实支撑单位判据识别有效坐标零集及仿射补集。没有 Cartier、截面、有效性、支撑等式、正次数或覆盖 input。", "file": "ProjPolynomialSections.lean", "decl": "exists_actual_projective_space_cartier_sections", "related": ["mvPolynomial_degree_zero_adjoin_variables"], "deps": ["projgenerators"], "status": "done", "inputs": ["实际整概形 X 及闭嵌入 X→Proj R[T₀,…,Tₙ]。", "输出：实际 Cartier O(1) 图册及全部有效坐标截面几何数据。"], "steps": [["实际标准变量生成元", "多项式归纳证明次数零子环上的生成性。", "mvPolynomial_degree_zero_adjoin_variables"], ["实际坐标覆盖构造", "齐次比方程、stalk 单位、坐标有效性和精确支撑全部构造。", "exists_actual_projective_space_cartier_sections"]]});
Object.assign(find('antiample'),{"title": "E 的存在性：射影构造已验证", "statement": "仿射正规双有理底上的实际射影闭嵌入，构造有效 Cartier E，覆盖所有 exceptional 素分量，且 E 在每条完整压缩曲线上严格负。", "scope": "由实际 Proj 坐标构造 O(1) 的截面覆盖，完整曲线不能位于仿射非零集，故真实交数为正。取负、清分母得到有效 E，实际归零系数曲线排除 exceptional 系数为零。有效性、exceptional 覆盖和负交数全部为输出。没有给定 A、E、截面覆盖或数值正性 input。此节点证明的是仿射底上的存在性；一般底拼接仍独立待完成。", "status": "done", "file": "ProjectiveExceptionalWitness.lean", "decl": "exists_actual_projective_exceptional_cartier", "related": [], "deps": ["projectivesections", "affinesectionpositive", "cartierinverse", "effectivetwist", "effectiveexceptional"], "inputs": ["任意特征代数闭域；正规整 X、Y，仿射 Y，X 紧，f proper birational。", "实际标准射影空间闭嵌入。", "E 有效性、exceptional 正系数及实际压缩曲线的负交数均为输出。"], "steps": [["构造 O(1)", "实际齐次坐标给 Cartier 截面与仿射非零覆盖。", "exists_actual_projective_space_cartier_sections"], ["真实正次数与取负", "完整曲线必遇有效坐标零除子，得到真实正次数。", "complete_integral_curve_positive_of_affine_section_cover"], ["清分母与覆盖", "主移动后有效，归零系数的实际曲线给矛盾。", "exists_effective_exceptional_covering_cartier_twist"], ["完整 E 存在定理", "由实际射影嵌入直接输出 E 的所有性质。", "exists_actual_projective_exceptional_cartier"]]});
Object.assign(find('intersection'),{"title": "真实交数与射影坐标正性：已验证", "statement": "相对 nef 按实际压缩完整曲线定义。实际射影坐标构造及仿射开集论证给出 O(1) 的正交数。", "scope": "实际 Cartier/R-Cartier 交数、正规化、有效性符号、支撑正性和相对 nef 符号已完成。射影空间坐标现在构造实际截面数据，不再要求给定截面覆盖。真实完整曲线必须遇有效坐标零除子，故得到正次数。这里没有数值正性假设。", "status": "done", "deps": ["nefpull", "affinesectionpositive", "cartierinverse", "projectivesections"], "inputs": ["实际完整曲线和构造出的 Cartier 坐标除子。", "−D f-nef 按被 f 压缩的实际曲线定义。", "O(1) 真实正次数由已构造的射影截面和仿射非零集推导。"], "steps": [["相对 nef 定义", "仅测试被 f 压缩的实际完整曲线。", "actual_relative_nef_negative_iff"], ["实际坐标数据", "从标准射影空间闭嵌入构造截面覆盖。", "exists_actual_projective_space_cartier_sections"], ["实际几何正性", "完整曲线遇零除子，主移动不变给正次数。", "complete_integral_curve_positive_of_affine_section_cover"]]});
Object.assign(find('core'),{"title": "仿射底射影 negativity (1)：已验证", "statement": "仿射正规底上，实际 proper birational 映射及射影空间闭嵌入满足：f_*D 有效、−D f-nef ⇒ D 有效。", "scope": "这是真实几何的仿射底版本，实权重任意，Cartier 图册索引任意，曲线允许奇异和非正规，特征任意。O(1) 实际方程和截面、正次数、有效 E、exceptional 覆盖与实际曲线全部在证明内构造，不作为输入。剩余完整定理工作：一般底的仿射局部拼接、proper 情形的 Chow 归约，以及第二部分的实际纤维连通性。完整主定理仍明确未完成。", "status": "done", "file": "ActualProjectiveAffineNegativity.lean", "decl": "actual_projective_affine_negativity", "related": ["actual_negativity_of_affine_section_cover", "actual_negativity_of_strictly_negative_cartier", "actual_negativity_of_antiample_witness"], "deps": ["max", "actualnegativecenter", "curves", "antiample", "intersection", "projectivesections"], "inputs": ["任意特征代数闭域；正规整 X、Y，仿射 Y，X 紧，f proper birational，Y 局部有限型。", "实际有限 Cartier 家族和任意实权重 D；实际 f_*D 有效、−D f-nef。", "实际闭嵌入 X→Proj Γ(Y,O_Y)[T₀,…,Tₙ]；没有 Cartier 截面或 E 见证输入。", "剩余：一般底的局部拼接、Chow 归约、实际纤维连通性。"], "steps": [["实际射影构造", "从齐次坐标构造所有实际 Cartier 截面数据。", "exists_actual_projective_space_cartier_sections"], ["有效 E 与覆盖", "从实际射影嵌入输出有效 E 及全部 exceptional 正系数。", "exists_actual_projective_exceptional_cartier"], ["真实曲线反证", "最大比值与归零系数，实际压缩曲线和真实交数给矛盾。", "actual_negativity_of_strictly_negative_cartier"], ["仿射底完整第一部分", "无需额外几何见证的实际 R-Cartier negativity。", "actual_projective_affine_negativity"]]});
Object.assign(find('effectiveexceptional'),{"status": "done", "scope": "给定实际严格负 Cartier 除子，构造有效 E，并证明全部 exceptional 素系数为正。这个输入已由实际射影空间坐标构造及真实曲线正性推出；完整组合见 E 存在定理节点。E 有效性与覆盖均不是 input。"});
Object.assign(find('affinesectionpositive'),{"scope": "选一个曲线泛点不消失的实际有效截面；完整曲线必遇其零除子，实际有效支撑正性与主除子移动不变给原除子严格正次数。实际射影空间闭嵌入到这些几何截面数据也已在 projectivesections 节点构造。"});

nodes.push({"id": "opencartier", "title": "实际开集限制：除子系数不变", "statement": "固定实际 Cartier 拉回到开子概形，整数及实 Weil 系数等于原系数。", "scope": "使用实际开嵌入的 stalk 同构及余维不变证明局部 DVR 阶数一致，再对有限实权重相加。没有限制系数相容 input。", "inputs": ["使用实际开嵌入的 stalk 同构及余维不变证明局部 DVR 阶数一致，再对有限实权重相加。没有限制系数相容 input。"], "steps": [["实际开集限制：除子系数不变", "使用实际开嵌入的 stalk 同构及余维不变证明局部 DVR 阶数一致，再对有限实权重相加。没有限制系数相容 input。", "actual_real_cartier_open_restriction_cycle"]], "file": "CartierOpenRestriction.lean", "decl": "actual_real_cartier_open_restriction_cycle", "related": ["actual_cartier_open_restriction_coefficient"], "deps": ["cartiercurve", "realpresentation"], "status": "done", "x": 278, "y": 21000, "paper": "projective1"});

nodes.push({"id": "openpush", "title": "限制 actual f_*D 的有效性", "statement": "proper birational 映射和除子限制到实际非空底开集后，推出仍有效。", "scope": "余维一处真实同构识别实际推出系数和严格变换系数；开集 stalk 阶数兼容给限制系数。其余余维推出系数由 mapCoeff 为零。", "inputs": ["余维一处真实同构识别实际推出系数和严格变换系数；开集 stalk 阶数兼容给限制系数。其余余维推出系数由 mapCoeff 为零。"], "steps": [["限制 actual f_*D 的有效性", "余维一处真实同构识别实际推出系数和严格变换系数；开集 stalk 阶数兼容给限制系数。其余余维推出系数由 mapCoeff 为零。", "actual_real_cartier_pushforward_effective_on_open"]], "file": "ActualOpenPushforward.lean", "decl": "actual_real_cartier_pushforward_effective_on_open", "related": ["actual_weil_cycle_pushforward_isWeil"], "deps": ["opencartier", "codimone", "actualnegativecenter"], "status": "done", "x": 278, "y": 21150, "paper": "projective1"});

nodes.push({"id": "opennef", "title": "相对 nef 在实际底开集上保持", "statement": "实际 R-Cartier 除子的相对 nef 限制到任意非空目标开集。", "scope": "实际完整曲线通过开嵌入仍完整，其压缩条件由真实交换关系搬运。固定实际 Cartier 拉回的正规化交数复合公式给完全相同的交数。", "inputs": ["实际完整曲线通过开嵌入仍完整，其压缩条件由真实交换关系搬运。固定实际 Cartier 拉回的正规化交数复合公式给完全相同的交数。"], "steps": [["相对 nef 在实际底开集上保持", "实际完整曲线通过开嵌入仍完整，其压缩条件由真实交换关系搬运。固定实际 Cartier 拉回的正规化交数复合公式给完全相同的交数。", "actual_relative_nef_on_target_open"]], "file": "ActualOpenNef.lean", "decl": "actual_relative_nef_on_target_open", "related": [], "deps": ["opencartier", "nefpull"], "status": "done", "x": 278, "y": 21300, "paper": "projective1"});

nodes.push({"id": "relativeprojective", "title": "真实相对射影闭嵌入与底交换", "statement": "构造实际 P^n_R→Spec R 结构态射；闭嵌入与原 f 交换，并自动给实际 Cartier 截面数据。", "scope": "由真实次数零子环和底环 C 映射构造结构态射。射影条件只含实际 Scheme 闭嵌入与交换等式，不含除子、数值、截面或 negativity 结论。", "inputs": ["由真实次数零子环和底环 C 映射构造结构态射。射影条件只含实际 Scheme 闭嵌入与交换等式，不含除子、数值、截面或 negativity 结论。"], "steps": [["真实相对射影闭嵌入与底交换", "由真实次数零子环和底环 C 映射构造结构态射。射影条件只含实际 Scheme 闭嵌入与交换等式，不含除子、数值、截面或 negativity 结论。", "actual_relative_projective_embedding_cartier_sections"]], "file": "RelativeProjectiveEmbedding.lean", "decl": "actual_relative_projective_embedding_cartier_sections", "related": [], "deps": ["projectivesections"], "status": "done", "x": 278, "y": 21450, "paper": "projective1"});
Object.assign(find('projective'),{"title": "射影 negativity (1)：一般底已验证", "statement": "任意特征代数闭域上的正规簇，实际 proper birational 且相对射影的 f，若 −D 为 f-nef，则 D 有效当且仅当实际 f_*D 有效。", "scope": "实际 R-Cartier 第一部分已全部接通，包括一般正规底和等价的正反两方向。相对射影性只要求在实际仿射底开集上有与 f 交换的真实标准 Proj 闭嵌入。开集系数、推出有效性、相对 nef 的限制兼容均已证明，局部 O(1)、截面、正次数、有效 E、exceptional 覆盖及实际曲线全部在证明中构造。没有仿射底、E、截面、数值正性、局部有效性或交数相容 input。完整 Theorem 1.4 的 proper Chow 归约及第二部分实际纤维连通性仍未完成。", "status": "done", "file": "ActualProjectiveNegativityIff.lean", "decl": "actual_projective_negativity_effectivity_iff", "related": ["actual_projective_negativity_part_one"], "deps": ["core", "opencartier", "openpush", "opennef", "relativeprojective"], "inputs": ["任意特征代数闭域；正规整 X、Y；实际 f proper birational，底局部有限型。", "相对射影性：在真实仿射底开集上有与 f 交换的标准 Proj 闭嵌入。", "任意有限实际 Cartier 家族与实权重表示 D；−D 为实际 f-nef。", "结论：D≥0 ⇔ 实际 f_*D≥0。此节点只为完整 proper 双结论定理的第一部分射影步骤。"], "steps": [["实际仿射限制", "Cartier 系数、推出有效性和相对 nef 均保持。", "actual_real_cartier_pushforward_effective_on_open"], ["仿射底真实证明", "实际 Proj 坐标构造 O(1) 及全部 E 几何数据。", "actual_projective_affine_negativity"], ["一般底拼接", "在每个实际点像的仿射邻域应用真实局部定理，再用限制系数一致性。", "actual_projective_negativity_part_one"], ["有效性等价", "真实推出保持有效给正向，几何 negativity 给反向。", "actual_projective_negativity_effectivity_iff"]]});
Object.assign(find('core'),{"scope": "真实仿射底版本已验证，全部 Cartier 截面、正次数、有效 E、exceptional 覆盖和实际曲线均在证明中构造。一般正规底的仿射拼接也已在射影 negativity (1) 节点完成。完整 proper 定理仍需 Chow 归约及第二部分的实际纤维连通性。"});

nodes.push({"id": "properfunctions", "title": "proper 双有理：仿射开集的函数下降", "statement": "正规底上的实际 proper birational f，在非空仿射底开集上的实际函数拉回为双射。", "scope": "由实际函数域同构取反像，再由余维一 stalk 同构证明各局部阶数非负，正规仿射环延拓给实际正则函数。没有 H⁰ 有限性、直接像等式或连通性 input。", "inputs": ["由实际函数域同构取反像，再由余维一 stalk 同构证明各局部阶数非负，正规仿射环延拓给实际正则函数。没有 H⁰ 有限性、直接像等式或连通性 input。"], "steps": [["proper 双有理：仿射开集的函数下降", "由实际函数域同构取反像，再由余维一 stalk 同构证明各局部阶数非负，正规仿射环延拓给实际正则函数。没有 H⁰ 有限性、直接像等式或连通性 input。", "proper_normal_birational_affine_functions_bijective"]], "file": "ProperBirationalFunctions.lean", "decl": "proper_normal_birational_affine_functions_bijective", "related": ["birational_functionField_pullback_bijective"], "deps": ["codimone", "normalsections"], "status": "done", "x": 278, "y": 22000, "paper": "fiber"});

nodes.push({"id": "structuresheaf", "title": "实际结构层：𝒪_Y ≅ f_*𝒪_X", "statement": "proper 双有理态射到正规局部 Noetherian 整概形，其实际自然结构层映射为同构。", "scope": "实际仿射基上的函数下降已证明；真实 sheaf basis 同构定理粘合，空开集由层的终对象性质处理。没有预设 f_*𝒪_X=𝒪_Y；纤维连通仍需 proper 形式函数。", "inputs": ["实际仿射基上的函数下降已证明；真实 sheaf basis 同构定理粘合，空开集由层的终对象性质处理。没有预设 f_*𝒪_X=𝒪_Y；纤维连通仍需 proper 形式函数。"], "steps": [["实际结构层：𝒪_Y ≅ f_*𝒪_X", "实际仿射基上的函数下降已证明；真实 sheaf basis 同构定理粘合，空开集由层的终对象性质处理。没有预设 f_*𝒪_X=𝒪_Y；纤维连通仍需 proper 形式函数。", "proper_normal_birational_structure_sheaf_isIso"]], "file": "ProperBirationalStructureSheaf.lean", "decl": "proper_normal_birational_structure_sheaf_isIso", "related": [], "deps": ["properfunctions"], "status": "done", "x": 278, "y": 22150, "paper": "fiber"});

nodes.push({"id": "propersections", "title": "任意实际底开集：函数唯一下降", "statement": "实际 pullback Γ(Y,U)→Γ(X,f⁻¹U) 对任意开集 U 为双射，包括非仿射及空开集。", "scope": "通过实际层同构的忘却函子和真实自然变换分量得到 IsIso(f.app U)，再取具体范畴的双射。没有指定抽象下降环映射。", "inputs": ["通过实际层同构的忘却函子和真实自然变换分量得到 IsIso(f.app U)，再取具体范畴的双射。没有指定抽象下降环映射。"], "steps": [["任意实际底开集：函数唯一下降", "通过实际层同构的忘却函子和真实自然变换分量得到 IsIso(f.app U)，再取具体范畴的双射。没有指定抽象下降环映射。", "proper_normal_birational_open_functions_bijective"]], "file": "ProperBirationalSections.lean", "decl": "proper_normal_birational_open_functions_bijective", "related": ["proper_normal_birational_open_functions_isIso"], "deps": ["structuresheaf"], "status": "done", "x": 278, "y": 22300, "paper": "fiber"});

nodes.push({"id": "schemeidempotents", "title": "实际概形：开闭分解与幂等元", "statement": "实际非平凡开闭分解在真实全局截面环中构造非平凡幂等元；若只有平凡幂等元则实际概形连通。", "scope": "结构层在不交开集上的真实粘合给 Γ(X,U∪V)≅Γ(X,U)×Γ(X,V)。构造 (1,0) 的逆像并验证。并未断言实际 proper 纤维的截面环已只有平凡幂等元。", "inputs": ["结构层在不交开集上的真实粘合给 Γ(X,U∪V)≅Γ(X,U)×Γ(X,V)。构造 (1,0) 的逆像并验证。并未断言实际 proper 纤维的截面环已只有平凡幂等元。"], "steps": [["实际概形：开闭分解与幂等元", "结构层在不交开集上的真实粘合给 Γ(X,U∪V)≅Γ(X,U)×Γ(X,V)。构造 (1,0) 的逆像并验证。并未断言实际 proper 纤维的截面环已只有平凡幂等元。", "actual_scheme_connected_of_global_idempotents_trivial"]], "file": "SchemeClopenIdempotent.lean", "decl": "actual_scheme_connected_of_global_idempotents_trivial", "related": ["actual_clopen_nontrivial_global_idempotent"], "deps": [], "status": "done", "x": 278, "y": 22450, "paper": "fiber"});

nodes.push({"id": "clopencharacteristic", "title": "实际开闭特征截面与拉回相容", "statement": "实际开闭集 S 的唯一特征正则函数在 S 上的 germ 为 1，在外部为 0；真实拉回保持此截面。", "scope": "从实际层粘合构造，germ 扩张唯一性证明幂等性和真实 pullback 相容。没有幂等元相容式 input。", "inputs": ["从实际层粘合构造，germ 扩张唯一性证明幂等性和真实 pullback 相容。没有幂等元相容式 input。"], "steps": [["实际开闭特征截面与拉回相容", "从实际层粘合构造，germ 扩张唯一性证明幂等性和真实 pullback 相容。没有幂等元相容式 input。", "actual_clopen_characteristic_pullback"]], "file": "ClopenCharacteristicSection.lean", "decl": "actual_clopen_characteristic_pullback", "related": ["actual_clopen_characteristic_exists_unique", "actual_clopen_characteristic_germ", "actual_clopen_characteristic_idempotent"], "deps": ["schemeidempotents"], "status": "done", "x": 278, "y": 22600, "paper": "fiber"});

nodes.push({"id": "infinitesimals", "title": "真实无穷小加厚：相容非平凡幂等元", "statement": "实际闭子概形若有非平凡开闭分解，在各实际理想层幂次加厚的函数逆极限中构造非平凡幂等元。", "scope": "实际 I^(n+1) 子概形、与原闭支撑的同胚、真实 inclusion 及函数逆极限全部构造。特征截面拉回给各阶相容，不是假设相容。尚未证明 proper 非仿射形式函数比较。", "inputs": ["实际 I^(n+1) 子概形、与原闭支撑的同胚、真实 inclusion 及函数逆极限全部构造。特征截面拉回给各阶相容，不是假设相容。尚未证明 proper 非仿射形式函数比较。"], "steps": [["真实无穷小加厚：相容非平凡幂等元", "实际 I^(n+1) 子概形、与原闭支撑的同胚、真实 inclusion 及函数逆极限全部构造。特征截面拉回给各阶相容，不是假设相容。尚未证明 proper 非仿射形式函数比较。", "actual_infinitesimal_nontrivial_idempotent"]], "file": "InfinitesimalIdempotents.lean", "decl": "actual_infinitesimal_nontrivial_idempotent", "related": ["actual_power_thickening_inclusion_point"], "deps": ["clopencharacteristic"], "status": "done", "x": 278, "y": 22750, "paper": "fiber"});

nodes.push({"id": "affinethickening", "title": "实际仿射加厚的商环与转移", "statement": "实际仿射 X 上 Γ(X_n,𝒪)≅Γ(X,𝒪)/I^(n+1)，真实加厚限制等于商环转移映射。", "scope": "使用实际 ideal-subsheme 结构层商环同构，并通过真实 inclusion 的复合等式验证转移相容。需要源 X 仿射；只假定底仿射不足。", "inputs": ["使用实际 ideal-subsheme 结构层商环同构，并通过真实 inclusion 的复合等式验证转移相容。需要源 X 仿射；只假定底仿射不足。"], "steps": [["实际仿射加厚的商环与转移", "使用实际 ideal-subsheme 结构层商环同构，并通过真实 inclusion 的复合等式验证转移相容。需要源 X 仿射；只假定底仿射不足。", "actual_affine_thickening_sections_transition"]], "file": "AffineThickeningSections.lean", "decl": "actual_affine_thickening_sections_transition", "related": ["actual_affine_thickening_sections_pullback"], "deps": ["infinitesimals"], "status": "done", "x": 278, "y": 22900, "paper": "fiber"});

nodes.push({"id": "affineformalfunctions", "title": "仿射形式函数：真实完备化比较", "statement": "实际仿射 X 的真实 adic 完备化，向实际幂次加厚函数逆极限的规范映射为双射。", "scope": "实际商环同构构造规范比较映射；零阶商环为零，其余阶从相容家族恢复，证明单射和满射。没有抽象比较或相容 input。这仅是仿射源版本，proper 非仿射全局比较仍待完成，完整 negativity lemma 尚未完成。", "inputs": ["实际商环同构构造规范比较映射；零阶商环为零，其余阶从相容家族恢复，证明单射和满射。没有抽象比较或相容 input。这仅是仿射源版本，proper 非仿射全局比较仍待完成，完整 negativity lemma 尚未完成。"], "steps": [["仿射形式函数：真实完备化比较", "实际商环同构构造规范比较映射；零阶商环为零，其余阶从相容家族恢复，证明单射和满射。没有抽象比较或相容 input。这仅是仿射源版本，proper 非仿射全局比较仍待完成，完整 negativity lemma 尚未完成。", "actual_affine_formal_functions_bijective"]], "file": "AffineFormalFunctions.lean", "decl": "actual_affine_formal_functions_bijective", "related": ["completion_power_quotient_eval", "completion_power_quotient_transition", "adic_completion_power_eval_transition"], "deps": ["affinethickening"], "status": "done", "x": 278, "y": 23050, "paper": "fiber"});
Object.assign(find('connected'),{"title": "proper 实际纤维连通：全局形式函数待补", "statement": "实际 f_*𝒪_X=𝒪_Y 及各阶加厚的相容幂等元已经证明。剩余证明 proper 非仿射源的全局形式函数比较，才能推出实际纤维连通。", "scope": "正规底的 proper 双有理实际结构层同构已通过，任意开集上的函数下降已通过。实际开闭分解的特征截面及其拉回、实际幂次加厚中的相容非平凡幂等元也已通过。仿射源上的真实 adic 完备化比较已通过，但 proper 的源通常非仿射，不能用它冒充全局形式函数。仍缺：在局部底 R=𝒪_Y,y 上，R̂≅lim_n Γ(X×_Spec R Spec(R/m^(n+1)),𝒪) 的实际全局比较及纤维识别。此节点和完整定理继续标为未完成。高维相交曲线选择已完成。", "deps": ["structuresheaf", "propersections", "infinitesimals", "affineformalfunctions", "localidempotents"], "inputs": ["已完成：实际自然结构层同构 𝒪_Y→f_*𝒪_X，以及任意开集上的实际函数双射。", "已完成：真实开闭特征截面、拉回相容、实际幂次加厚的函数逆极限中的非平凡幂等元。", "已完成：源 X 仿射时的规范 adic 完备化比较。", "待完成：proper 非仿射源的全局形式函数比较 R̂≅lim_n Γ(X_n,𝒪_Xn)，及实际纤维的对应。"], "steps": [["实际结构层同构：已完成", "余维一同构和正规仿射延拓证明函数下降，真实层基定理粘合。", "proper_normal_birational_structure_sheaf_isIso"], ["实际加厚中的相容幂等元：已完成", "各阶实际幂次加厚保留同一闭支撑，特征截面真实拉回证明相容。", "actual_infinitesimal_nontrivial_idempotent"], ["仿射形式函数：已完成", "仿射源的真实完备化比较为双射，不等于 proper 非仿射版本。", "actual_affine_formal_functions_bijective"], ["proper 全局形式函数：待完成", "证明局部底上的 R̂ 与实际无穷小纤维函数逆极限的规范比较；再接实际纤维识别。"], ["局部环矛盾：已验证", "完备局部环没有非平凡幂等元，得到连通性。", "localRing_idempotent_trivial"]]});

nodes.push({"id": "projchartquot", "title": "实际射影仿射图：有限型商环", "statement": "R 为交换环，B 为有限型 R-代数。构造某个实际 D₊(X₀) 的坐标环到 B 的满射 R-代数映射。", "scope": "R 为交换环，B 为有限型 R-代数。构造某个实际 D₊(X₀) 的坐标环到 B 的满射 R-代数映射。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["R 为交换环，B 为有限型 R-代数。构造某个实际 D₊(X₀) 的坐标环到 B 的满射 R-代数映射。"], "steps": [["实际射影仿射图：有限型商环", "R 为交换环，B 为有限型 R-代数。构造某个实际 D₊(X₀) 的坐标环到 B 的满射 R-代数映射。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "exists_actual_projective_affine_chart_quotient"]], "file": "ProjectiveAffineChartAlgebra.lean", "decl": "exists_actual_projective_affine_chart_quotient", "related": ["actual_projective_chart_evaluation_constant", "actual_projective_chart_evaluation_coordinate"], "deps": [], "status": "done", "x": 278, "y": 23500, "paper": "proper"});

nodes.push({"id": "affineprojimmersion", "title": "仿射有限型态射：实际射影浸入", "statement": "实际 X、Y 仿射，f:X→Y 局部有限型。构造某个 n 及与 f 交换的实际 X→ℙⁿ_Γ(Y) 浸入；不声称仿射 X 的此浸入闭。", "scope": "实际 X、Y 仿射，f:X→Y 局部有限型。构造某个 n 及与 f 交换的实际 X→ℙⁿ_Γ(Y) 浸入；不声称仿射 X 的此浸入闭。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["实际 X、Y 仿射，f:X→Y 局部有限型。构造某个 n 及与 f 交换的实际 X→ℙⁿ_Γ(Y) 浸入；不声称仿射 X 的此浸入闭。"], "steps": [["仿射有限型态射：实际射影浸入", "实际 X、Y 仿射，f:X→Y 局部有限型。构造某个 n 及与 f 交换的实际 X→ℙⁿ_Γ(Y) 浸入；不声称仿射 X 的此浸入闭。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "exists_actual_affine_finite_type_projective_immersion"]], "file": "FiniteTypeProjectiveImmersion.lean", "decl": "exists_actual_affine_finite_type_projective_immersion", "related": ["actual_projective_affine_chart_inclusion_over"], "deps": ["projchartquot"], "status": "done", "x": 278, "y": 23650, "paper": "proper"});

nodes.push({"id": "standardprojproper", "title": "标准相对射影空间：实际 proper", "statement": "任意交换环 R 与 n，真实 Proj(R[X₀,…,Xₙ])→Spec R 为 proper；degree-zero 环与 R 的同构在证明中构造。", "scope": "任意交换环 R 与 n，真实 Proj(R[X₀,…,Xₙ])→Spec R 为 proper；degree-zero 环与 R 的同构在证明中构造。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["任意交换环 R 与 n，真实 Proj(R[X₀,…,Xₙ])→Spec R 为 proper；degree-zero 环与 R 的同构在证明中构造。"], "steps": [["标准相对射影空间：实际 proper", "任意交换环 R 与 n，真实 Proj(R[X₀,…,Xₙ])→Spec R 为 proper；degree-zero 环与 R 的同构在证明中构造。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "actual_standard_projective_space_proper"]], "file": "StandardProjectiveProper.lean", "decl": "actual_standard_projective_space_proper", "related": ["projective_degree_zero_inclusion_bijective"], "deps": ["projgenerators"], "status": "done", "x": 278, "y": 23800, "paper": "proper"});

nodes.push({"id": "hartshornecover", "title": "Hartshorne：有限仿射覆盖与公共开集", "statement": "X 整且拟紧，Y 仿射，实际 f 局部有限型。构造有限非空仿射覆盖、各片实际射影浸入以及所有片的非空公共开集。", "scope": "X 整且拟紧，Y 仿射，实际 f 局部有限型。构造有限非空仿射覆盖、各片实际射影浸入以及所有片的非空公共开集。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["X 整且拟紧，Y 仿射，实际 f 局部有限型。构造有限非空仿射覆盖、各片实际射影浸入以及所有片的非空公共开集。"], "steps": [["Hartshorne：有限仿射覆盖与公共开集", "X 整且拟紧，Y 仿射，实际 f 局部有限型。构造有限非空仿射覆盖、各片实际射影浸入以及所有片的非空公共开集。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "exists_actual_hartshorne_affine_projective_cover"]], "file": "HartshorneAffineCover.lean", "decl": "exists_actual_hartshorne_affine_projective_cover", "related": [], "deps": ["affineprojimmersion", "standardprojproper"], "status": "done", "x": 278, "y": 23950, "paper": "proper"});

nodes.push({"id": "hartshornefinite", "title": "Hartshorne 图像：第二投影有限", "statement": "在实际整 Noetherian X 的 proper 图像构造中，各仿射片有实际射影浸入并与公共有理映射交换。构造整图像 Z，π:Z→X proper、双有理、满射，q:Z→P 有限。", "scope": "在实际整 Noetherian X 的 proper 图像构造中，各仿射片有实际射影浸入并与公共有理映射交换。构造整图像 Z，π:Z→X proper、双有理、满射，q:Z→P 有限。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["在实际整 Noetherian X 的 proper 图像构造中，各仿射片有实际射影浸入并与公共有理映射交换。构造整图像 Z，π:Z→X proper、双有理、满射，q:Z→P 有限。"], "steps": [["Hartshorne 图像：第二投影有限", "在实际整 Noetherian X 的 proper 图像构造中，各仿射片有实际射影浸入并与公共有理映射交换。构造整图像 Z，π:Z→X proper、双有理、满射，q:Z→P 有限。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "hartshorne_graph_second_projection_finite"]], "file": "HartshorneProjectionFinite.lean", "decl": "hartshorne_graph_second_projection_finite", "related": ["actual_graph_projection_isImmersion"], "deps": ["hartshornegraph", "zmtfinite"], "status": "done", "x": 278, "y": 24100, "paper": "proper"});

nodes.push({"id": "affineproductcharts", "title": "实际纤维积：仿射坐标图", "statement": "S 仿射，X→S、Y→S 任意，U⊂X、V⊂Y 仿射开。实际 X×_S Y 中的 pr₁⁻¹U∩pr₂⁻¹V 是仿射开。", "scope": "S 仿射，X→S、Y→S 任意，U⊂X、V⊂Y 仿射开。实际 X×_S Y 中的 pr₁⁻¹U∩pr₂⁻¹V 是仿射开。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["S 仿射，X→S、Y→S 任意，U⊂X、V⊂Y 仿射开。实际 X×_S Y 中的 pr₁⁻¹U∩pr₂⁻¹V 是仿射开。"], "steps": [["实际纤维积：仿射坐标图", "S 仿射，X→S、Y→S 任意，U⊂X、V⊂Y 仿射开。实际 X×_S Y 中的 pr₁⁻¹U∩pr₂⁻¹V 是仿射开。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "actual_affine_product_chart"]], "file": "AffineProductCharts.lean", "decl": "actual_affine_product_chart", "related": [], "deps": [], "status": "done", "x": 278, "y": 24250, "paper": "proper"});

nodes.push({"id": "properproduct", "title": "实际有限相对乘积：构造与仿射图", "statement": "有限个实际 proper Tᵢ→S，构造真实相对乘积 P→S 及投影、泛性质。若 S 仿射，各 Tᵢ 的仿射开集的同时逆像是 P 的仿射开。", "scope": "有限个实际 proper Tᵢ→S，构造真实相对乘积 P→S 及投影、泛性质。若 S 仿射，各 Tᵢ 的仿射开集的同时逆像是 P 的仿射开。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["有限个实际 proper Tᵢ→S，构造真实相对乘积 P→S 及投影、泛性质。若 S 仿射，各 Tᵢ 的仿射开集的同时逆像是 P 的仿射开。"], "steps": [["实际有限相对乘积：构造与仿射图", "有限个实际 proper Tᵢ→S，构造真实相对乘积 P→S 及投影、泛性质。若 S 仿射，各 Tᵢ 的仿射开集的同时逆像是 P 的仿射开。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "exists_actual_finite_proper_relative_product"]], "file": "FiniteProperRelativeProduct.lean", "decl": "exists_actual_finite_proper_relative_product", "related": [], "deps": ["affineproductcharts"], "status": "done", "x": 278, "y": 24400, "paper": "proper"});

nodes.push({"id": "hartshornemodification", "title": "Hartshorne：实际有限乘积改造", "statement": "X 整、局部 Noetherian，Y 仿射，实际 f proper。内部构造有限覆盖、公共有理映射和图像，得到整 Z、proper 双有理满射 π:Z→X 及到实际射影乘积的有限 q。", "scope": "X 整、局部 Noetherian，Y 仿射，实际 f proper。内部构造有限覆盖、公共有理映射和图像，得到整 Z、proper 双有理满射 π:Z→X 及到实际射影乘积的有限 q。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["X 整、局部 Noetherian，Y 仿射，实际 f proper。内部构造有限覆盖、公共有理映射和图像，得到整 Z、proper 双有理满射 π:Z→X 及到实际射影乘积的有限 q。"], "steps": [["Hartshorne：实际有限乘积改造", "X 整、局部 Noetherian，Y 仿射，实际 f proper。内部构造有限覆盖、公共有理映射和图像，得到整 Z、proper 双有理满射 π:Z→X 及到实际射影乘积的有限 q。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "exists_actual_hartshorne_finite_modification"]], "file": "HartshorneFiniteModification.lean", "decl": "exists_actual_hartshorne_finite_modification", "related": [], "deps": ["hartshornecover", "hartshornefinite", "properproduct"], "status": "done", "x": 278, "y": 24550, "paper": "proper"});

nodes.push({"id": "birationalcomp", "title": "实际双有理态射：复合", "statement": "实际整概形间的分离局部有限型双有理态射复合仍双有理。由 generic stalk 同构构造真实非空同构开集。", "scope": "实际整概形间的分离局部有限型双有理态射复合仍双有理。由 generic stalk 同构构造真实非空同构开集。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["实际整概形间的分离局部有限型双有理态射复合仍双有理。由 generic stalk 同构构造真实非空同构开集。"], "steps": [["实际双有理态射：复合", "实际整概形间的分离局部有限型双有理态射复合仍双有理。由 generic stalk 同构构造真实非空同构开集。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "actual_birational_morphism_comp"]], "file": "BirationalComposition.lean", "decl": "actual_birational_morphism_comp", "related": ["birational_of_actual_generic_stalk_isIso"], "deps": ["codimone"], "status": "done", "x": 278, "y": 24700, "paper": "proper"});

nodes.push({"id": "normalhartshorne", "title": "Hartshorne：实际正规改造", "statement": "任意特征代数闭域，X 整且局部 Noetherian，Y 仿射有限型，f proper。构造正规整局部 Noetherian N、proper 双有理满射 π:N→X，以及到实际射影乘积的有限态射。", "scope": "任意特征代数闭域，X 整且局部 Noetherian，Y 仿射有限型，f proper。构造正规整局部 Noetherian N、proper 双有理满射 π:N→X，以及到实际射影乘积的有限态射。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["任意特征代数闭域，X 整且局部 Noetherian，Y 仿射有限型，f proper。构造正规整局部 Noetherian N、proper 双有理满射 π:N→X，以及到实际射影乘积的有限态射。"], "steps": [["Hartshorne：实际正规改造", "任意特征代数闭域，X 整且局部 Noetherian，Y 仿射有限型，f proper。构造正规整局部 Noetherian N、proper 双有理满射 π:N→X，以及到实际射影乘积的有限态射。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "exists_actual_normal_hartshorne_modification"]], "file": "NormalHartshorneModification.lean", "decl": "exists_actual_normal_hartshorne_modification", "related": [], "deps": ["hartshornemodification", "birationalcomp", "normalizationfinite", "normalizationbirational", "normalizationnormal"], "status": "done", "x": 278, "y": 24850, "paper": "proper"});

nodes.push({"id": "productcartier", "title": "实际射影乘积：Cartier 截面覆盖", "statement": "整 X 有实际有限 q:X→P，P 的有限射影因子坐标图满足已证明的仿射交集性质。构造实际 Cartier 图册、有效截面、支撑等式及仿射非零覆盖。", "scope": "整 X 有实际有限 q:X→P，P 的有限射影因子坐标图满足已证明的仿射交集性质。构造实际 Cartier 图册、有效截面、支撑等式及仿射非零覆盖。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["整 X 有实际有限 q:X→P，P 的有限射影因子坐标图满足已证明的仿射交集性质。构造实际 Cartier 图册、有效截面、支撑等式及仿射非零覆盖。"], "steps": [["实际射影乘积：Cartier 截面覆盖", "整 X 有实际有限 q:X→P，P 的有限射影因子坐标图满足已证明的仿射交集性质。构造实际 Cartier 图册、有效截面、支撑等式及仿射非零覆盖。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "exists_actual_projective_product_cartier_sections"]], "file": "ProjectiveProductCartierSections.lean", "decl": "exists_actual_projective_product_cartier_sections", "related": [], "deps": ["projpullback", "properproduct"], "status": "done", "x": 278, "y": 25000, "paper": "proper"});

nodes.push({"id": "canonicalpushpull", "title": "同一规范实际拉回：π_*π*D=D", "statement": "正规整局部 Noetherian 概形间 π proper 双有理，D 是任意有限实 Cartier 和。与交数和 nef 使用同一规范拉回，实际 Weil cycle 满足 π_*π*D=D。", "scope": "正规整局部 Noetherian 概形间 π proper 双有理，D 是任意有限实 Cartier 和。与交数和 nef 使用同一规范拉回，实际 Weil cycle 满足 π_*π*D=D。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["正规整局部 Noetherian 概形间 π proper 双有理，D 是任意有限实 Cartier 和。与交数和 nef 使用同一规范拉回，实际 Weil cycle 满足 π_*π*D=D。"], "steps": [["同一规范实际拉回：π_*π*D=D", "正规整局部 Noetherian 概形间 π proper 双有理，D 是任意有限实 Cartier 和。与交数和 nef 使用同一规范拉回，实际 Weil cycle 满足 π_*π*D=D。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "actual_canonical_real_cartier_push_pull"]], "file": "CanonicalCartierPushPull.lean", "decl": "actual_canonical_real_cartier_push_pull", "related": [], "deps": ["pushpull", "canonicalrealpullback"], "status": "done", "x": 278, "y": 25150, "paper": "proper"});

nodes.push({"id": "birationalcyclecomp", "title": "实际双有理 Weil 推出：复合", "statement": "p:Z→X、f:X→Y proper 双有理，X、Y 正规整局部 Noetherian。任意实际 Weil cycle E 满足 (f∘p)_*E=f_*(p_*E)，余维一性质在证明中推出。", "scope": "p:Z→X、f:X→Y proper 双有理，X、Y 正规整局部 Noetherian。任意实际 Weil cycle E 满足 (f∘p)_*E=f_*(p_*E)，余维一性质在证明中推出。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["p:Z→X、f:X→Y proper 双有理，X、Y 正规整局部 Noetherian。任意实际 Weil cycle E 满足 (f∘p)_*E=f_*(p_*E)，余维一性质在证明中推出。"], "steps": [["实际双有理 Weil 推出：复合", "p:Z→X、f:X→Y proper 双有理，X、Y 正规整局部 Noetherian。任意实际 Weil cycle E 满足 (f∘p)_*E=f_*(p_*E)，余维一性质在证明中推出。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "actual_proper_birational_weil_pushforward_comp"]], "file": "BirationalCycleComposition.lean", "decl": "actual_proper_birational_weil_pushforward_comp", "related": ["actual_cycle_push_at_codimension_one_preimage"], "deps": ["strict", "codimone", "birationalcomp"], "status": "done", "x": 278, "y": 25300, "paper": "proper"});

Object.assign(find("chow"),{"id": "chow", "title": "Hartshorne 正规改造与实际截面：已验证", "statement": "任意特征代数闭域上，Y 仿射有限型、X 整局部 Noetherian、f proper。构造实际正规整 N、proper 双有理满射 π:N→X，并构造 N 上实际 Cartier 仿射截面覆盖。", "scope": "任意特征代数闭域上，Y 仿射有限型、X 整局部 Noetherian、f proper。构造实际正规整 N、proper 双有理满射 π:N→X，并构造 N 上实际 Cartier 仿射截面覆盖。 按 Hartshorne 构造实际有限图像，再有限正规化，并以射影乘积坐标的相乘方程构造截面。negativity 第一部分所需的改造与截面已全部证明；此节点不宣称另行完成一般 Chow 引理的 Segre 闭嵌入。完整双结论定理仍需实际纤维连通性。", "inputs": ["任意特征代数闭域上，Y 仿射有限型、X 整局部 Noetherian、f proper。构造实际正规整 N、proper 双有理满射 π:N→X，并构造 N 上实际 Cartier 仿射截面覆盖。"], "steps": [["Hartshorne 正规改造与实际截面：已验证", "任意特征代数闭域上，Y 仿射有限型、X 整局部 Noetherian、f proper。构造实际正规整 N、proper 双有理满射 π:N→X，并构造 N 上实际 Cartier 仿射截面覆盖。 按 Hartshorne 构造实际有限图像，再有限正规化，并以射影乘积坐标的相乘方程构造截面。negativity 第一部分所需的改造与截面已全部证明；此节点不宣称另行完成一般 Chow 引理的 Segre 闭嵌入。完整双结论定理仍需实际纤维连通性。", "exists_actual_hartshorne_cartier_modification"]], "file": "HartshorneCartierModification.lean", "decl": "exists_actual_hartshorne_cartier_modification", "related": [], "deps": ["normalhartshorne", "productcartier"], "status": "done", "x": 278, "y": 25450, "paper": "proper"});

nodes.push({"id": "properaffine", "title": "proper negativity (1)：仿射底已验证", "statement": "任意特征代数闭域，X、Y 正规整局部 Noetherian，Y 仿射有限型，f proper 双有理。任意有限实 Cartier 和 D，若 −D 为 f-nef 且实际 f_*D≥0，则 D≥0。", "scope": "任意特征代数闭域，X、Y 正规整局部 Noetherian，Y 仿射有限型，f proper 双有理。任意有限实 Cartier 和 D，若 −D 为 f-nef 且实际 f_*D≥0，则 D≥0。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["任意特征代数闭域，X、Y 正规整局部 Noetherian，Y 仿射有限型，f proper 双有理。任意有限实 Cartier 和 D，若 −D 为 f-nef 且实际 f_*D≥0，则 D≥0。"], "steps": [["proper negativity (1)：仿射底已验证", "任意特征代数闭域，X、Y 正规整局部 Noetherian，Y 仿射有限型，f proper 双有理。任意有限实 Cartier 和 D，若 −D 为 f-nef 且实际 f_*D≥0，则 D≥0。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "actual_proper_affine_negativity_part_one"]], "file": "ActualProperAffineNegativity.lean", "decl": "actual_proper_affine_negativity_part_one", "related": [], "deps": ["chow", "canonicalpushpull", "birationalcyclecomp", "nefpull", "effectiveexceptional", "affinesectionpositive"], "status": "done", "x": 278, "y": 25600, "paper": "proper"});

nodes.push({"id": "properone", "title": "proper negativity (1)：一般底已验证", "statement": "任意特征代数闭域，X、Y 正规整局部 Noetherian，Y 有限型，f proper 双有理。任意有限实 Cartier 和 D，若 −D 为 f-nef 且实际 f_*D≥0，则 D≥0。不要求 f projective。", "scope": "任意特征代数闭域，X、Y 正规整局部 Noetherian，Y 有限型，f proper 双有理。任意有限实 Cartier 和 D，若 −D 为 f-nef 且实际 f_*D≥0，则 D≥0。不要求 f projective。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["任意特征代数闭域，X、Y 正规整局部 Noetherian，Y 有限型，f proper 双有理。任意有限实 Cartier 和 D，若 −D 为 f-nef 且实际 f_*D≥0，则 D≥0。不要求 f projective。"], "steps": [["proper negativity (1)：一般底已验证", "任意特征代数闭域，X、Y 正规整局部 Noetherian，Y 有限型，f proper 双有理。任意有限实 Cartier 和 D，若 −D 为 f-nef 且实际 f_*D≥0，则 D≥0。不要求 f projective。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "actual_proper_negativity_part_one"]], "file": "ActualProperNegativity.lean", "decl": "actual_proper_negativity_part_one", "related": [], "deps": ["properaffine", "opencartier", "openpush", "opennef"], "status": "done", "x": 278, "y": 25750, "paper": "proper"});

nodes.push({"id": "properiff", "title": "proper negativity (1)：完整等价式已验证", "statement": "任意特征代数闭域上的正规簇，f proper 双有理，D 为有限实 Cartier 和，−D 为 f-nef。则 D≥0 ⇔ 实际 f_*D≥0。第一部分完成；独立的纤维支撑第二部分仍未完成。", "scope": "任意特征代数闭域上的正规簇，f proper 双有理，D 为有限实 Cartier 和，−D 为 f-nef。则 D≥0 ⇔ 实际 f_*D≥0。第一部分完成；独立的纤维支撑第二部分仍未完成。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "inputs": ["任意特征代数闭域上的正规簇，f proper 双有理，D 为有限实 Cartier 和，−D 为 f-nef。则 D≥0 ⇔ 实际 f_*D≥0。第一部分完成；独立的纤维支撑第二部分仍未完成。"], "steps": [["proper negativity (1)：完整等价式已验证", "任意特征代数闭域上的正规簇，f proper 双有理，D 为有限实 Cartier 和，−D 为 f-nef。则 D≥0 ⇔ 实际 f_*D≥0。第一部分完成；独立的纤维支撑第二部分仍未完成。 所列通常定理条件均须满足。此声明已实际编译与内核审计；完整 Theorem 1.4 的第二部分仍需实际纤维连通性。", "actual_proper_negativity_effectivity_iff"]], "file": "ActualProperNegativityIff.lean", "decl": "actual_proper_negativity_effectivity_iff", "related": [], "deps": ["properone", "geomcycle"], "status": "done", "x": 278, "y": 25900, "paper": "proper"});
Object.assign(find("proper"),{"title": "Proper negativity lemma：第一部分已完成", "statement": "最终双结论目标：第一部分实际 proper 有效性等价式已验证；第二部分实际纤维支撑二择一仍待完成。", "scope": "第一部分已完整证明，无 projective、改造、E、截面或曲线 input。第二部分已有实际连通完整概形上的支撑二择一，但还须证明 proper 双有理态射的实际纤维连通性。完整 Theorem 1.4 继续保留未完成状态。", "deps": ["properiff", "projective2"], "inputs": ["已完成：实际 proper negativity (1)，D≥0 ⇔ 实际 f_*D≥0。", "待完成：proper 双有理实际纤维连通性，以及第二部分的最终衔接。"], "steps": [["第一部分：已验证", "Hartshorne 正规改造和实际截面、实际交数、nef 拉回及推出下降全部接通。", "actual_proper_negativity_effectivity_iff"], ["第二部分：仍未完成", "证明 proper 双有理实际纤维连通性，再应用已验证的实际支撑二择一。"]], "status": "pending"});
find("properreduce").scope="此节点保留抽象归约组合。其所需实际改造、nef、推拉和有效性第一部分现已由独立 properiff 节点全部完成；完整第二部分仍需实际纤维连通性。";
find("projective").scope += " 后续 proper 第一部分已完成，见 properiff；第二部分实际纤维连通性仍未完成。";
