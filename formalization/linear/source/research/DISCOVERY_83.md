# Discovery 83: homogeneous generic bases and growth comparisons

Online discovery used the official mathlib documentation and original
leanprover-community/mathlib4 repository. Focused searches covered finite
graded-module rank, homogeneous generators, generic bases, localization,
common denominators and finite torsion annihilators.

- [Localized modules](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/LocalizedModule/Basic.html)
- [Localization finiteness](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Finiteness.html)
- [Module support](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Support.html)

Exact APIs were checked in the pinned mathlib commit
`2a885768dae569d938bb9ff3474da6a8753bb90a` before use:

- `span_eq_top_of_isLocalizedModule`;
- `Submodule.exists_fun_fin_finrank_span_eq`;
- `Submodule.localized'_span`;
- `Submodule.toLocalizedQuotient'` and its actual localization instance;
- `Submodule.annihilator_top_inter_nonZeroDivisors` for the finite torsion quotient;
- `Module.isTorsionBy_quotient_iff`;
- `LinearIndependent.restrict_scalars'`, `.of_comp`, and `.eq_coords_of_eq`;
- `Module.finrank_pi_fintype` and actual linear-map rank inequalities.

The online results did not directly supply the desired original projective
pullback growth comparison. This is not a claim that no formalization exists
elsewhere. The missing bridges were proved using actual internal gradings,
coordinate quotient components and the original finite cone pullback.

Every private module is compiled and checked by source SHA before promotion;
the full public build and axiom audit must pass before publication. No
`m=q^growthDegree` or `D=q^dim(V)` claim is made at this checkpoint.
