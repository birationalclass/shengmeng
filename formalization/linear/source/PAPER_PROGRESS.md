# 当前论文与 Lean 形式化的对应情况

核对对象：`output/luo-1005-revision-20261006/Luo_1005-20261006.tex`。统计和核验时间以本项目 `snapshot.json`、`full-audit.json` 为准。

**完整 Linearity Theorem 尚未证明。** 本报告按论文的数学结论划分完成情况，不把辅助声明的数量换算成完成百分比。后文“代数核心完成”也不表示其几何应用所需的连接已经全部完成。

| 当前论文 | 已核验内容 | 尚未闭合的依赖 |
|---|---|---|
| 第一节 Setup 1.4 与主证明 | 原齐次映射、实际全不变素理想、射影点集、实际图表拉回及函数域；一般完整纤维有限、约化，点数等于实际函数域像域扩张次数；原映射迭代的次数乘法；最后的数值矛盾 | `D=q^dim(V)`，Bertini 选取，实际概形和几何维数比较，实际 Cartier/Bézout 交叉数不等式 |
| 第二节，引理 2.1 | **精确局部代数目标已证明**：`Ann_A(N)=BΔ`；对任意允许的参数提升，商环 Artinian，其极大理想的 socle 由非零 Δ 生成 | 应用该引理时，从原几何设定统一构造这些局部完全交模型与参数条件 |
| 第三节，引理 3.1 和 Claim 3.2 | 实际仿射完全交的完美乘法配对、低次数消失、Jacobian 迹公式、在明确局部 socle 条件下的非零加权点关系；光滑点的形式坐标和若干射影图表转换 | 将 Setup 的完整实际纤维与上述局部模型全部连接，统一推出原稿中对所有次数 t 齐次多项式成立的关系 |
| 第四节，引理 4.1、4.2 | 若干对偶、限制、非零性及支撑的代数机制 | 实际 canonical sheaf 的固定扭转嵌入、几何 Koszul、proper duality、Serre 消失和只依赖嵌入的统一次数多项式提升；**这一节的主要几何证明仍开放** |
| 主定理完整证明 | 最后的数值蕴含已有 Lean 证明；原目标已用实际射影线性子空间精确表述 | 完整几何输入仍未从原 f,V 推出，故没有完整主定理证明 |

## 第二节完成的确切含义

`Linear/Target.lean` 中的 `Lemma31Goal` 和 `Linear/ArbitraryParameterSocle.lean` 中的 `lemma31_complete` 保留了**旧稿编号**，它们对应当前论文的**引理 2.1**。

形式化只要求原稿的正维数、正法向维数、方程正则序列、有限平坦性、约化为参数环，以及允许的参数生成条件。配对、新参数作用、有限自由性、非零性和 socle 生成均在证明中构造，不作为额外结论输入。

因此第二节局部引理确实是一块已经完成的数学结果；但这不等于第三节的几何应用已经自动完成。

## 第三节为什么还不能标为完成

`Linear/AffineOriginRelation.lean` 和 `Linear/AffinePointRelation.lean` 已证明实际多项式完全交上的加权点关系。其完整类型仍明确保留各点局部 socle 生成等条件。

已有 `Linear/SmoothProjectiveFormalSocle.lean` 等模块推进实际光滑图表与形式模型的连接。仍需把**同一个原映射、同一个 Setup 纤维、同一组局部方程**接起来，才能宣布原稿的引理 3.1 完成。用另一组抽象满足条件的数据不能代替这一步。

## 当前正在补的次数步骤

从原坐标商构造了实际 Hilbert 多项式 P、累计 Hilbert 多项式 C，并证明 `deg(C)=deg(P)+1`。实际锥拉回泛秩已经算出为 `q^deg(C)`。

新增的锥/比值域连接进一步证明：

1. 锥模的实际泛秩等于原锥函数域像域扩张次数。
2. 原缩放映射固定整个射影坐标比值域 E。
3. 原非零缩放坐标 z₀ 在 E 上超越，且原锥函数域实际同构于 `E(z₀)`。
4. 原拉回满足 `f*(z₀)=u z₀^q`，其中非零 u 在 E 中，并证明相应单变量子扩张的次数是 q。

仍需完成**整个像域的系数扩张比较**，再将 `deg(P)` 识别为几何 `dim(V)`，才得到实际射影纤维的 `q^dim(V)` 个点。这里的单变量次数计算不是完整的射影次数公式。

## 主证明最后一步仍需什么

论文需要实际构造 Q，使其次数 m 与迭代无关、在 V 上不恒为零并在其他纤维消失；还需要从有效 Cartier 除子和正确相交推出

`q^r ≤ q^(r-1) d m < q^r`。

这条不等式导致矛盾的纯数值部分已核验；**把左侧交叉数不等式作为假设输入**只证明了条件蕴含，不能算已经完成论文中的交叉理论。

英文状态摘要：The exact relative-Jacobian local algebra lemma is complete. Affine residue/relation cores and substantial original-map fiber and field constructions are checked. The full projective relation, uniform geometric sheaf lifting, actual intersection inequality and final Linearity Theorem remain open.
