# Checkpoint 109 library discovery and exact scope

Online official mathlib documentation reviewed:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPolynomial/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Projectivization/Basic.html

Pinned implementations of linear independence, polynomial evaluation/substitution,
homogeneous aeval and actual projective representative scaling were inspected.
The source linear forms w0*Xi-wi*X0 are proved independent by actual evaluation;
injectivity of the SAME finite projection transfers independence to the original
coordinate ring. Their actual projective zero points are compared to the actual
linear section, not an unrelated abstract family.

The degree-q pullbacks are homogeneous by existing mathlib homogeneous aeval.
Vanishing at the actual projective image is compared to pullback vanishing using
the actual representative scaling. Total invariance then proves that their
common projective point set on V equals the union of ALL original whole fibers
over the section targets. No point-set comparison is assumed as an input.

Scope remains POINT sets. Equality of nonreduced schemes, the reduced regular
intersection and the remaining Section 4/global geometry are NOT discharged.
The exact full Linearity Theorem remains UNPROVED.
