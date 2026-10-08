# Checkpoint 88: actual dimension and actual differential/local parameters

Pinned Lean 4.35.0-rc3 and mathlib 2a885768dae569d938bb9ff3474da6a8753bb90a.

Focused online searches for an existing Kähler-rank/Krull or transcendence-degree
comparison did not locate a directly applicable implementation. Primary official
documentation and the pinned source inspected before the new bridge:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Etale/Kaehler.html
  `tensorKaehlerEquivOfFormallyEtale` and actual localized differentials.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Kaehler/Polynomial.html
  `mvPolynomialBasis`, the actual polynomial differential basis.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Etale/Field.html
  `FormallyEtale.of_isSeparable`, with no essential-finite-type extra hypothesis.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Integral.html
  `isAlgebraic_of_isFractionRing`, actual compatible integral/fraction towers.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/TensorProduct/Basis.html
  Actual basis base change and transport by a linear equivalence.

Also read pinned Etale/Basic, FractionRing.liftAlgebra and its scalar-tower instance,
PerfectField separability, and the user project's LocalizedDifferentialRank,
ProjectiveSmoothPointParameters and ProjectiveWholeFiberKrullPower. Search results
from historical discussions were not used as mathematical proof sources.

Proof route: take an ACTUAL finite injective normalization k[X_1,...,X_s] -> A.
Construct its compatible map and fraction-field lift to F=Frac(A). Integrality
gives algebraicity over E=Frac(k[X]); characteristic zero gives separability and
formal etaleness. Actual localization followed by that extension gives the
canonical base-change differential equivalence. The actual polynomial basis,
base-changed and transported, computes dim_F Omega(F/k)=s. Localized differential
rank gives rank_A Omega(A/k)=s; the actual normalization dimension result gives
ringKrullDim A=s. Global smoothness of A is NOT assumed.

Apply this to the original nonempty projective chart: its Hilbert degree,
Krull dimension and differential rank are the SAME integer. Actual target
polynomial parameters at every original smooth chart point have this cardinality.
One aggregate theorem gives this SAME dimension for those local parameters and
EVERY original iterate's WHOLE general fibers, with no supplied dimension or
cardinality formula.

This closes a dimension connection between Sections 1 and 3. It does not yet
assemble all local normal/radical equations and the actual Jacobian polynomial
on the SAME full Setup fiber; Section 3's original homogeneous relation, global
Proj comparison, Bertini, Section 4 sheaf/Koszul/duality/Serre, Cartier/Bezout and
the full Linearity Theorem remain open. Private/public compilation and exact-type
axiom audits are required before release.
