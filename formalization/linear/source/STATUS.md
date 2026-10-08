# Linearity 形式化：当前状态

完整 Linearity Theorem 尚未证明。`LinearityTheoremGoal : Prop` 是精确目标定义，不是证明。论文原稿未修改。

## 本地核验

最近内核审计：2026-10-08T22:06:49+08:00。1175 条 theorem/lemma 证明、226 个定义；380 个 Lean 源文件。共审核 1597 个含移植的声明，仅使用 propext、Classical.choice、Quot.sound，没有 sorryAx 或项目新公理。Checkpoint 87 全项目编译、公理审计通过。

## 与当前论文的对应

详细逐节分析见 [PAPER_PROGRESS.md](PAPER_PROGRESS.md)。旧 Lean 名称 `lemma31_complete` 对应当前论文的引理 2.1。

- 第二节引理 2.1 的精确局部代数目标已证明：Ann(N)=BΔ；每个允许的参数提升后，商环 Artinian，其 socle 由非零 Δ 生成。新参数作用、完全交方程商、有限自由性和配对均在证明中构造。
- 第三节已有实际仿射完全交的完美配对、低次数消失、Jacobian 迹公式及明确局部 socle 条件下的非零权重关系。射影图表与实际光滑点的形式坐标连接已推进，但完整 Setup 纤维到原关系引理的统一连接仍待证。
- 原 f,V 已构造共同好目标开集，其上每个完整点纤维有限、约化、由互异光滑点组成，点数等于实际原射影函数域拉回像域次数 D；迭代后次数为 D^k。现已证明 D=q^deg(P)，其中 P 为实际非零 Hilbert 多项式；完整迭代纤维点数为 (q^k)^deg(P)。已证明 deg(P)=实际仿射图表的 Krull 维数 r，故完整迭代纤维有 (q^k)^r 个点。全局 Proj/Scheme 维数比较仍待证明。
- 实际齐次坐标商的 Hilbert–Serre、多项式 P、累计多项式 C、deg(C)=deg(P)+1、原泛基、统一分母、双向增长比较及锥泛秩 q^deg(C) 已证明。
- Checkpoint 85 把该锥泛秩连接到原锥函数域像域次数。实际缩放映射固定整个射影比值域 E；原非零缩放坐标 z₀ 在 E 上超越，原锥域实际同构于 E(z₀)。原拉回满足 f*(z₀)=u z₀^q，非零 u 在 E 中，单变量子扩张次数为 q。
- Checkpoint 86 已完成整个原锥像域与射影像域的系数扩张比较，证明锥次数等于 q 乘射影次数，并把实际射影/图表次数及每次迭代的完整纤维点数算为 Hilbert 多项式次数的幂。
- Checkpoint 87 从实际 Noether normalization 及原坐标过滤的双向增长证明 Hilbert 次数等于实际图表 Krull 维数，同时识别实际 Spec 拓扑维数；原映射完整次数为 q^r，所有迭代的完整一般纤维点数为 (q^k)^r。
- 第四节的主要几何论证仍开放：canonical sheaf 固定扭转嵌入、几何 Koszul、proper duality、Serre 统一次数界与齐次多项式提升。代数对偶辅助证明不代替这些几何结论。
- 主证明最后的数值矛盾已证明；实际 Cartier/Bézout 交叉数不等式仍待证。

## 下一项主证明依赖

将已证明的实际图表 Krull 维数 r 与局部参数构造所用的实际微分模秩识别，统一第一节纤维点数和第三节局部模型的维数；全局 Proj/Scheme 比较仍待证。原稿 Bertini、关系、几何对偶提升和交叉数接口仍需完成。

## 已验证发布

冻结发布：20261008-linear-42，提交 91fbe32133c9b940772cd013f7cf186f6b104045。线上包含 1148 条项目证明、224 个定义和 364 个 Lean 文件；共审计 1568 个声明。云端 Lean 与 Pages 均成功。中英文原迭代完整纤维点数、原映射完整类型、卡片自身 34 行及源码 SHA 元数据已核验。提交源码包内全部 364 个 Lean 文件与 Git 一致；没有重新下载线上源码包或逐一比对全部静态资源。完整主定理仍未证明。

入口：https://birationalclass.github.io/shengmeng/visuals/linear/

约 30 分钟检查一次实质发布资格，没有后台自动续跑。历史证据保存在 MILESTONE_*.md、DISCOVERY 记录和冻结源码包；这些历史文件的当时开放项应按最新状态解读。
