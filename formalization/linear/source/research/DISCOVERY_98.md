# Checkpoint 98: degree system and actual zero-locus residues

The full Linearity Theorem remains UNPROVED.

Official online code discovery:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/PDeriv.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Degrees.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPolynomial/Homogeneous.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient/Operations.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dual/Defs.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Nullstellensatz.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Equiv.html

Pinned mathlib: 2a885768dae569d938bb9ff3474da6a8753bb90a.
Read exact pinned types before adapting code. Reuse homogeneous-component
and rename exchange, support coefficients of derivatives, finite sums and
determinant bounds, actual quotientEquivAlg, and LinearEquiv.dualMap.
Reuse the project's previously audited regular highest-system construction,
localization of annihilators, affine complete-intersection perfect pairing,
maximal residue evaluations and actual polynomial-point equivalence.

Uncovered bridges:

1. Origin-only zero locus under an actual polynomial coordinate equivalence
   fixing the origin.
2. Actual source linear changes and independent invertible target combinations
   preserve the degree-q highest system; its regularity constructs each
   individual equation's exact degree.
3. The same normal Jacobian has degree at most c(q-1), proved from derivative
   support and determinant degree.
4. Identify the original centered whole-fiber numerators with these very
   transformed equations.
5. Insert original geometric outputs and every-maximal-ideal socles into one
   same equation/Jacobian system for every original iterate; derive the
   global nilradical annihilator. None of these outputs is an added input.
6. Transport the actual multiplication pairing through an actual quotient
   algebra equivalence, including its low-degree vanishing.
7. Construct actual zero-locus weights from actual maximal residues; all
   weights are nonzero. The algebraic relation is conditional on the explicit
   highest system and global annihilator and still needs insertion into the
   original whole-fiber homogeneous statement.

No equality of the reduced in-V fiber algebra and ambient equation algebra
is used. Normal nilpotents are retained.
Positive actual chart dimension remains explicit in the original iterator.
Simultaneous Bertini fiber union, original homogeneous relation, global
Proj/Scheme comparison, Section 4 sheaf lifting and actual intersection
inequality are not claimed as complete.
