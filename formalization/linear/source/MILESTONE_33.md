# Milestone 33: genuine formal inverse and smooth equation coordinates

The actual Jacobian determinant at zero being a unit now implies that zero-constant equations generate the full maximal ideal. The proof constructs a coefficient matrix, identifies its constant matrix with the actual derivative matrix, proves its determinant a unit, and uses its actual matrix inverse. Existing audited parameter-substitution constructions then give a genuine power-series algebra automorphism.

For a full-rank normal Jacobian minor, this gives `smoothFormalCoordinateEquiv`: all tangential variables and all tangential series are fixed, and normal variables map to the given equations. `smoothFormalQuotientEquiv` identifies the actual equation ideal quotient with the tangential power-series ring and proves the canonical element formula and the parameter-series formula.

No nilpotent truncation is substituted for the full ring. No generation hypothesis is added. Field assumptions are arbitrary; finite variable sets and a nonempty normal index set are explicit. Deriving the local equations and unit minor from the manuscript geometry, as well as the thickened relative finite-flat presentation, is still unfinished.

Library discovery inspected pinned and official mathlib MvPowerSeries substitution, Matrix nonsingular inverse, Smooth/AdicCompletion and Smooth/StandardSmoothCotangent. The latter smooth-lifting and cotangent results do not directly supply the needed full formal coordinate isomorphism. We reuse the audited project coefficient expansion, parameter substitution and nested-coordinate chart, proving only the uncovered Jacobian-to-generator and quotient bridges.

Sources inspected:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPowerSeries/Substitution.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Smooth/AdicCompletion.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Smooth/StandardSmoothCotangent.html

The full Linearity Theorem is still unproved. Counts await full public build and audit.
