# Proof overview and packaging / 证明概览与卡包规则

The overview shows substantive mathematical stages, not the final Lean theorem's first forwarding lemma. Nagata's overview contains scaled source sections, the geometric contradiction, full theorem assembly, and the effective-curve bridge. The short final reformulations remain accessible in the full connection graph and source inspector.

Stacked covers represent coherent subproofs containing at least two substantive child steps. A single theorem, equivalence bridge, forwarding result, or leaf appears as an ordinary card. A genuine one-premise argument may open its actual goal and premise without a stacked cover. Right-click or Shift+F10 on a leaf reads its information instead of entering an empty world.

Overview membership is stored separately from exact proof dependencies. Overview wires are reading routes, not new direct Lean dependencies. Ordinary cards count their own declaration and proof; genuine packs count merged source ranges from their actual project-code dependency closure. No verification status changes with packaging.

默认概览展示数学证明的主要阶段，不机械地只展示最终 Lean 声明的第一个转述引理。Nagata 顶层直接展示缩放源截面、几何矛盾、全定理装配和有效曲线桥接；最终转述仍保留在完整连接图和源码详情中。

至少有两个实质子步骤的完整子论证才显示堆叠卡包。单个定理、等价桥接、转述和叶节点使用普通卡片。一前提的真实论证可以展开实际目标与前提，但不显示堆叠封面。叶节点右击或 Shift+F10 查看信息，不进入空证明界面。

概览成员与实际证明依赖分开保存；概览连线表示阅读路线。普通卡只统计自身声明和证明，真实卡包才统计去重后的项目依赖区间。封装方式不改变核验状态。
