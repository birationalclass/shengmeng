# 当前论文与 Lean 形式化的对应情况

核对原稿：output/luo-1005-revision-20261006/Luo_1005-20261006.tex。
当前已核验检查点：102；全项目编译和公理审计时间：2026-10-09T03:28:41+08:00。

**完整 Linearity Theorem 尚未证明。** 按论文的结论和假设判断进度，不将辅助声明数量换算成完成百分比。

| 当前论文 | 已核验内容 | 尚未闭合的依赖 |
|---|---|---|
| 第一节 Setup 1.4 | **部分完成**：原齐次映射、全不变性、仿射图表与函数域；同一实际维数 r；原映射次数 q^r；每次原迭代的一条完整良好纤维有 (q^k)^r 个点；原 V 的 r+1 个一次形式、单射有限锥映射、实际维数和无基点性均已构造 | Bertini 同时选取 d 个目标点及其纤维并集；与全局 Proj/Scheme 的比较 |
| 第二节，引理 2.1 | **引理完整证明**：Ann_A(N)=BΔ；任意允许的参数商中，非零 Δ 生成 socle | 引理本身已完成；第三节的所有原稿几何应用须另行接通 |
| 第三节，引理 3.1、Claim 3.2 | **核心单纤维齐次关系已证明**：从每次原迭代构造非空良好目标开集；其完整纤维上，所有 t=r(q−1)−1 次齐次多项式满足同一非零系数关系 | 任意指定的非零齐次代表关系也已核验；明确保留 r>0、迭代次数 q>1 和良好目标开集的范围；还须接通 Setup 中的 Bertini 同时选取 |
| 第四节，引理 4.1、4.2 | **部分代数机制完成**：若干对偶、限制、支撑与条件提升结论 | 实际 canonical sheaf 固定扭转嵌入、几何 Koszul、proper duality、Serre 统一次数界和原齐次多项式 Q 的构造；主要几何证明仍开放 |
| 主定理证明的最后一步 | **数值蕴含完成**：所需交叉数不等式成立即产生矛盾；精确射影线性目标已定义 | 从实际有效 Cartier 除子、正确相交与 Bézout 推出不等式；全链尚未闭合 |

## 第一节新增的线性投影基础

Checkpoint 101–102 构造真正的线性 Noether normalization，
并接到原射影簇 V：存在 r+1 个一次齐次形式 L₀,…,Lᵣ，
它们给出的锥映射单射、模有限，在原射影簇上没有公共零点。
整映射、递归齐次核、实际维数和无基点性都在证明中推导。

这里 Hilbert 多项式的次数等于维数 r；其首项系数给出的 deg V=d
与一般线性截面点数的等同，是另一条尚未完成的结论。
一般截面恰有 d 个点及同时避开坏点集仍须证明，所以 Bertini Setup 仍标为部分完成。

## 第二节完成的是哪一个结果

Lean 中的 Lemma31Goal 和 lemma31_complete 保留旧稿编号，实际对应当前论文的引理 2.1。
有限自由性、参数作用、完美配对、Jacobian 非零性及 socle 生成在证明中推导，未把这些结论作为新的输入。
因此这一局部代数引理可以计为完整结果。

## 第三节现在推进到了哪里

当前原迭代入口是 LinearStudy.projective_iterates_whole_fibers_representative_relations
（Linear/ProjectiveFiberRepresentativeRelation.lean）。对同一原 f,V 的每次迭代，
它构造非空良好目标开集，而不是额外假定一个留数关系。对该开集内每个目标点，
当实际图表维数 r>0、迭代的齐次次数 q>1 时，得到完整纤维 S₁ 上

    λₓ ≠ 0 （所有 x∈S₁），
    Σₓ λₓ σ(1,x) = 0 （所有 t=r(q−1)−1 次齐次多项式 σ）。

原局部方程、共同法向坐标、同一个 Jacobian、所有极大理想覆盖、最高项条件、
次数界和留数配对均已在这一入口中从原数据推导。Checkpoint 100 进一步核验任意指定非零代表 vₓ 的关系：
由 [vₓ]=[1:x] 推出 vₓ₀≠0，再将 λₓ 改为 λₓ/(vₓ₀)^t，
得到 Σₓ λ′ₓ σ(vₓ)=0，所有 λ′ₓ 仍非零。这与原稿的代表约定一致。

这已完成第三节的核心单纤维关系；**不把它等同于全部 Setup 连接完成**。
还须严格构造同一次 Bertini 线性截面中的 d 个目标点及它们的同时纤维并集。

## 两种纤维代数不能混同

V 内的良好纤维商约化。留数计算使用环境空间中仅由纤维方程定义的商，
该商可保留法向幂零元。两者点集一致不代表环或理想相等。
当前证明保留这一区别，通过实际坐标、点集及商代数同构传递对应的配对。

## 第四节和主定理还缺什么

必须实际构造次数固定为 m、在 V 上不恒为零、在其他纤维上消失的 Q，
其中 m 与迭代无关；再从正确的交叉理论推出

    q^r ≤ q^(r−1) d m < q^r。

这个不等式产生矛盾的数值部分已核验；把左侧交叉数估计作为假设输入，
仅证明条件蕴含，不能计为论文的几何交叉数证明。

下一步接通 simultaneous Bertini Setup；
随后继续第四节的固定次数几何提升与最后交叉数。

English status: The exact relative-Jacobian lemma is complete. The original
single-good-whole-fiber homogeneous relation is verified for any chosen
nonzero representatives, with explicit positive dimension and degree assumptions.
Simultaneous Bertini selection, global scheme comparisons, uniform geometric
lifting, actual intersection and the final Linearity Theorem remain open.
