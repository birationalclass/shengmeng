# Checkpoint 99: original homogeneous whole-fiber relation

Official online discovery:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient/Operations.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Nullstellensatz.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Equiv.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dual/Defs.html

Pinned mathlib: 2a885768dae569d938bb9ff3474da6a8753bb90a.
The actual quotient algebra equivalence and scalar-point precomposition
give an actual zero-locus equivalence and explicit evaluation comparison.
No reducedness hypothesis or equality of the ambient/in-V quotient rings
is introduced.

Use the already audited original whole-fiber common coordinates, finite
ambient equation algebra, all-maximal Jacobian socles, transformed highest
system, c(q-1) Jacobian bound and global nilradical annihilator.
The previously verified actual reindexed perfect pairing and actual-zero-
locus weighted relation are inserted into THAT same original fiber.
Source-coordinate equivalence transports polynomial evaluation and degree
exactly. Original homogeneous polynomials are dehomogenized, giving
nonzero weights on the original in-V fiber for every polynomial homogeneous
of degree t=r(q-1)-1.

The original iterator constructs a nonempty good target open for every
iterate; the actual chart dimension remains explicit and must be positive,
and the chosen iterate must have degree greater than one. Points are the
entire actual affine fiber already compared with the whole original fiber
by the prior chart-avoidance construction, not an independent point family.
Vectors in this declaration use the normalized representative (1,x).
Arbitrary representatives are related by the existing homogeneous scaling
formula; their direct original-fiber wrapper is not claimed here.

This closes the original single-good-fiber relation assembly, rather than
adding the local, degree or residue conclusions as assumptions. It does
not construct simultaneous Bertini target intersections and their fiber
union, global Proj/Scheme comparison, Section 4 lifting or the actual
intersection inequality. The full Linearity Theorem remains UNPROVED.
