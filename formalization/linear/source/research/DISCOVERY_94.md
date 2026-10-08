# Centering actual targets and transporting original ideal powers

Primary online discovery read the official mathlib MvPolynomial.Rename
documentation, including actual renameEquiv types, evaluation and degree
comparison. The pinned local Ideal.Maps, Localization.AtPrime and existing
verified PolynomialRecentering/PolynomialFormalDerivative/LocalGeneratorsEquiv
types were inspected before constructing the new bridges.

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Rename.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Degrees.html

Actual local generators imply containment in the actual point ideal. Centering
the same original target transports local generators, their first jets and
the original ideal to the origin. The whole original iterate-fiber aggregate
retains this centered data at the SAME actual target with the SAME dimension.

The actual rational map centering square is derived from original numerator
and denominator formulas. Original ideal-power inequalities are transported
through actual target centering and source denominator-coordinate equivalence,
and genuine quotient-local unramification survives target centering.

No transformed power inequality, ideal containment, commutative square or new
unramification is assumed. These are required connections for the original
whole-fiber common-Jacobian assembly; that full assembly and homogeneous
relation are still OPEN, as are Bertini, Section 4 and actual intersection.
