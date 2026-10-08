# Library discovery for the original cone/projective field comparison

Pinned Lean: 4.35.0-rc3. Pinned mathlib: 2a885768dae569d938bb9ff3474da6a8753bb90a.

Online discovery and pinned local inspection preceded the new constructions:

1. `Mathlib/LinearAlgebra/Dimension/Localization.lean`: `IsFractionRing.finrank_eq`. Reused with carefully separated original source and pullback target scalar actions. No module-rank equality is supplied as a hypothesis.
2. `Mathlib/LinearAlgebra/Projectivization/Basic.lean`: `Projectivization.mk_eq_mk_iff`. Reused to prove actual homogeneous unit scaling fixes projective points.
3. `Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean`: `adjoin_induction`, `subset_adjoin`, `equivOfEq`, `topEquiv`. Reused to prove all ratio-field elements are fixed and construct the actual field isomorphism.
4. `Mathlib/Algebra/Polynomial/Roots.lean`: finiteness of the root set of a nonzero polynomial. The infinite scaling orbit then proves transcendence.
5. `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean`: `RatFunc.algEquivOfTranscendental`. Reused only after proving the original-coordinate transcendence and whole-field generation.
6. `Mathlib/FieldTheory/RatFunc/IntermediateField.lean`: `RatFunc.finrank_eq_max_natDegree`. Reused for the nonzero scaled monomial; no minimal-polynomial degree proof was recreated.
7. `Mathlib/LinearAlgebra/Dimension/Finrank.lean`: `Algebra.finrank_eq_of_equiv_equiv`. Reused to transfer the scaled-power degree through a compatible actual field isomorphism.
8. The online and pinned `RatFunc.finrank_ratFunc_ratFunc` coefficient-extension formula was found for the next missing comparison. It is **not yet** connected to the original cone image field, and finding its name does not discharge that comparison.

Primary online documentation:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/RatFunc/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/RatFunc/AsPolynomial.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/RatFunc/IntermediateField.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Projectivization/Basic.html

These are library discovery records, not claims that an already complete Linearity Theorem formalization was found. Project-specific original map, quotient, field-range and coordinate comparisons are new proofs.
