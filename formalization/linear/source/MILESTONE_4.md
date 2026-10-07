# General trace, parameter quotients and coefficient determinants

The full Linearity Theorem remains unproved. These results use actual mathlib
objects and introduce no custom axiom.

`TraceElement.lean` constructs the element dual to Algebra.trace under an
explicit perfect multiplication pairing. Over a reduced base with nilpotent
reduction kernel, it is the module rank times the dual reduction generator.
It annihilates that kernel and generates its annihilator when the rank is a
unit. It is nonzero over a characteristic-zero field. This does not identify
the trace element with the actual Jacobian: that residue/trace comparison
remains an explicit hypothesis of the final bridge.

`ParameterQuotient.lean` proves that arbitrary lifted parameters generating
the maximal ideal in the reduced base give a local Artinian quotient of a
Noetherian thickening. The image of the original nilradical is maximal and
equals the quotient nilradical. completeIntersection_parameterQuotient_artinian
applies to the exact power-series presentation of Lemma31Goal. It discharges
its Artinian and maximal-ideal conclusions, without flatness or socle inputs.
Jacobian survival and socle generation are still unproved.

`DeterminantAnnihilator.lean` derives determinant annihilation from M*x=0 by
the actual adjugate identity and passes it to the quotient by equations H=M*x.
`PowerSeriesCoefficients.lean` constructs that matrix for arbitrary zero-
constant-coefficient multivariable power series. Assign each monomial to a
variable occurring in it; prove that part divisible by the variable with
mathlib's coefficient criterion. It also proves that the augmentation kernel
is the variable ideal. Over a field the coordinate ideal in the actual
quotient is maximal and its annihilator contains the coefficient determinant.
Nonzero socle generation and derivative-Jacobian comparison are not asserted.

Library-first discovery reused the official online documentation and checked
the pinned full types for algebraic trace, ideal correspondence, Hopkins–
Levitzki, power-series local/Noetherian instances, adjugates, matrix map identities
and X_pow_dvd_iff. No applicable Scheja–Storch implementation was found in the
focused searches; this is not a global nonexistence claim. Original Koszul
sources from open PR 34913 are being inspected. Research .lean.txt files are
not imported or counted as formalization.

Sources:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Trace/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Maps.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/HopkinsLevitzki.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Adjugate.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPowerSeries/Basic.html

Next: regular-sequence comparison and nonvanishing for the coefficient
determinant, followed by comparison with the Jacobian or trace element.
This checkpoint is an intermediate result, not completion of the theorem.
