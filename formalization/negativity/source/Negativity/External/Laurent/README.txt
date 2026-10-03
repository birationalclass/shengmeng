外部代数几何 Lean 证明复用 / External algebraic-geometry proof reuse

来源 / Source:
https://github.com/Vilin97/Autoformalization
固定提交 / Pinned commit: 09497ebf6ee48ef49c4f3d24501954bc3a2855d6
目录 / Upstream directory: coherent-cohomology-finite/CoherentCohomologyFinite
许可证 / License: Apache-2.0; see LICENSE. All original copyright headers retained.
作者归属 / Attribution: Vasil V. and contributors; individual authors are recorded
in retained source headers where upstream supplied them.

选用范围 / Selected scope:
17 个原始文件构造射影 Laurent Čech 复形、指数收缩、有限生成、范畴上同调比较
及非负扭曲的正次消失。有限性只要求系数环 Noetherian；消失只要求交换环。
没有特征零、Z-平坦或几何比较假设。
These 17 original files construct the projective Laurent Cech complex,
exponent contraction, finite generation, categorical homology comparison
and positive-degree vanishing for nonnegative twists. Finiteness requires
a Noetherian coefficient ring; vanishing only requires a commutative ring.
No characteristic-zero or Z-flatness hypothesis is introduced.

工程入口 / Project entry points:
Negativity.ImportedProjectiveCechFiniteness.imported_projective_laurent_cech_cohomology_finite
Negativity.ImportedProjectiveCechVanishing.imported_projective_laurent_cech_positive_twist_vanishing

适配 / Adaptations:
重定位 imports，并适配当前 Lean 的 module/public import/public section 语法；
在两个范畴比较文件启用定义相等兼容选项，并将两个线性同构的原有返回类型显式写出。
原始文件和适配文件的 SHA-256 均见 sources.json。
Imports are relocated and adapted to current Lean module/public syntax.
Two categorical comparison files enable Lean
backward-definitional-equality compatibility options; two existing linear-equivalence
return types are annotated explicitly. Original and adapted
SHA-256 fingerprints are recorded in sources.json.

边界 / Scope boundary:
上述结论是显式 Laurent 复形的结论；仍须把它接到实际射影概形的结构层、
coherent 层、proper 分次上同调及形式函数。不把显式复形的验证冒充完整
negativity lemma 或 proper 上同调有限性的验证。
These results concern the explicit Laurent complex. Comparison with actual
projective structure sheaves, coherent sheaves, proper graded cohomology and
formal functions remains to be completed in our project. These imported
proofs do not complete the full negativity lemma or proper finiteness.

外部完整定理 / Upstream complete theorem:
MainTheorem.lean in the pinned upstream project states coherent cohomology
finiteness for actual proper schemes over Q. Its README reports a completed
build, but this entire upstream project has not been independently rebuilt
here. Its Q theorem and Z-flat geometric lemmas do not automatically cover
our arbitrary-characteristic algebraically closed base. Only the selected
17-file arbitrary-ring chain is incorporated into our local kernel audit.

优先复用的 mathlib / Already-used mathlib foundations:
Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean
Mathlib/AlgebraicGeometry/ValuativeCriterion.lean
Mathlib/AlgebraicGeometry/Normalization.lean
Mathlib/Algebra/Module/GradedModule.lean
