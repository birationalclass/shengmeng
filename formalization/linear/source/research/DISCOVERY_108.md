# Checkpoint 108 discovery and exact scope

Reviewed pinned mathlib's `MvPolynomial.IsHomogeneous`, homogeneous components,
`sum_homogeneousComponent`, rename/aeval and `Projectivization` normalization.
The online search for multivariate homogenization found the official univariate
Polynomial/Homogenize implementation; its type does not directly cover the
actual multivariate affine good-open equation. The minimal missing bridge is
proved from the existing homogeneous-component decomposition, not from a new
homogenization axiom.

Official references inspected:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Homogenize.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPolynomial/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Projectivization/Basic.html

Reused actual finite-map algebraicity and the already audited source-closed-set
avoidance theorem. Cone-fiber avoidance is proved through the actual rational
point kernel, then transported by actual degree-one homogeneous scaling to
the entire projective section. Homogenizing the original good-open equation
with an X0 factor proves that ALL section points lie in its actual affine open.
The existing Hilbert-degree section theorem and original whole-fiber relation
are combined only after comparing their actual chart Krull dimensions.

Output: one fixed original finite linear projection and d=degree V, with for
every original iterate a nonempty target open giving actual d-point sections,
ALL original complete fibers and homogeneous relations. No good point family,
degree equality, residue relation or generic-avoidance assertion is assumed.
Global Scheme intersection, transversality, pulled-back common-zero scheme,
Section 4 uniform geometric lifting and actual intersection remain OPEN.
The full Linearity Theorem is UNPROVED.
