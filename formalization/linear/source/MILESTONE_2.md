# Jacobian：第二阶段核验

本次确实证明了一元闭纤维情形，没有证明一般相对完全交引理或 Linearity Theorem。

## 精确结果

设 K 为特征零域，H∈K[[X]]，H≠0，H(0)=0。令 A=K[[X]]/(H)，δ=[H′]。Lean 已证明：

1. A 是 Artinian 环。
2. nilradical A 是极大理想。
3. Ann(nilradical A)=(δ)。
4. δ≠0。

第二条还蕴含 A 为局部环，因此第三条就是其 socle 的生成结论。完整 Lean 类型直接记录上述四条，不将局部性或生成元存在性作为输入。

声明：`LinearStudy.oneVariable_closedFiber_jacobian`，源码 `Linear/OneVariable.lean`。

## 证明路线

先用 mathlib 的幂级数阶数分解 H=uX^(s+1)，其中 s≥0、u 为单位。对实际商环 B[[X]]/(X^(s+1))，常数项商映射的核等于 (X)；B 约化时这也是全部零根。直接以幂级数系数计算其湮灭子为 (X^s)，并证明系数映射 b↦[C(b)]·[X^s] 为单射。

真实导数类为 (s+1)[X^s]。在特征零域上 s+1 可逆，因此它非零且生成相同湮灭子。商环的 Noetherian 性和极大零根给出维数零，进而由 mathlib 的 Hopkins–Levitzki 接口得到 Artinian 性。

最后 (H)=(X^(s+1))，且在该商环中

`[(uX^(s+1))′]=[u]·[(X^(s+1))′]`。

单位因子不改变生成理想及非零性，所以得到一般一元方程的结论。这里没有借用一个已假设的完美配对或 socle 生成元。

## 条件和边界

- 一元闭纤维结果允许任意特征零域，不要求代数闭；不限制方程重数。
- 单项式族 B[[X]]/(X^(s+1)) 的零根计算允许任意约化交换基环 B；导数生成还须 s+1 在 B 中可逆。
- 任意 H 的单位分解此处只在域上使用，不声称推广到任意基环。
- 一般多元完全交、任意参数提升后的非零性、全局 Euler–Jacobi 留数关系仍待形式化。这是一元特例的实际进展，不可作为一般引理的完成证明。

## 库接口

固定 mathlib 提交：`2a885768dae569d938bb9ff3474da6a8753bb90a`。

复用了 `PowerSeries.X_pow_dvd_iff`、`PowerSeries.X_dvd_iff`、`PowerSeries.coeff_order`、`PowerSeries.divXPowOrder`、`PowerSeries.isUnit_iff_constantCoeff`、`Ideal.span_singleton_mul_left_unit`、`RingHom.ker_isMaximal_of_surjective`、`Ring.KrullDimLE.of_isMaximal_nilradical` 及 `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`。导数使用 mathlib 的实际 Derivation，而非人工定义的 Jacobian 数值。

局部 socle/Gorenstein/Jacobian 搜索未找到直接满足一般相对引理的接口；这不构成“所有 Lean 库都没有该定理”的断言。

## 实际检查

`build.py` 编译两个新增模块和根模块，`audit.py` 重新检查全部完整类型及公理。现有 95 条 theorem/lemma 证明、31 个定义、126 个审计声明；公理仅为标准 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或自定义公理。

导出图谱共 42 个节点。新版一元闭纤维世界已检查中英文条件与结论、完整源码、右键和 Shift+F10 进入、父级返回、选卡保持 144% 缩放、拖动、滚轮缩放和 760px 窄窗口。浏览器错误／警告日志为空。线上状态以 `release.json` 为准。
