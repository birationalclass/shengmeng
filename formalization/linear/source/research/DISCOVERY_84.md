# Library discovery — polynomial growth and original generic rank

Online primary sources checked:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Polynomial/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Degree/Lemmas.html

Pinned source: mathlib 2a885768dae569d938bb9ff3474da6a8753bb90a.
Inspected exact types of Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq,
Polynomial.tendsto_atBot_of_leadingCoeff_nonpos, degree/leading-coefficient
composition, Nat cofinal casts and closed-order limit inequalities.

Existing code proves rational-function limits but does not connect them to
the project's original pullback module. The new bridge composes these actual
limits with natural degrees. The independently proved actual two-sided
filtered-dimension estimates are converted to polynomial inequalities.
Both limits force equality with q^(deg C). The original Hilbert polynomials
are constructed, rather than taken as arbitrary data, in the aggregate.

Private source SHA and actual compiler logs are recorded separately in
checkpoint84-private-provenance.json; all private proofs compiled with only
propext, Classical.choice and Quot.sound. Public build/audit is required before
freezing or publishing. Geometric dimension and projective degree remain open.
