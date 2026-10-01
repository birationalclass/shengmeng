export const statusLabels = {done:'✓ 模型内已验证',conditional:'◐ 条件式已验证',assumption:'◇ 暂作假设',pending:'○ 待完成目标'};
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
