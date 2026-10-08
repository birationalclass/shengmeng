# Checkpoint 97 library discovery and exact scope

Official online discovery inspected:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPolynomial/Homogeneous.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/LocalRing/ResidueField/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Maximal.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Eval.html

Pinned mathlib: 2a885768dae569d938bb9ff3474da6a8753bb90a.
The pinned source supplies homogeneous component projection, finite homogeneous
decomposition, projection of homogeneous elements, and rename/component exchange.
The project already proves actual finite algebra maximal residue maps,
coordinate evaluation, quotient homomorphism extensionality, and the original
ambient/in-V zero-locus comparison.

Uncovered bridges implemented:

1. Exact changed ORIGINAL ambient ideal, preserving normal nilpotents.
2. Every scalar point of the changed quotient recovers an original equation
   zero and its actual inverse coordinates.
3. Equality of actual quotient evaluations from generator values.
4. Coverage of every maximal ideal by an original point via its constructed
   scalar residue map; no point coverage or reducedness assumption.
5. Insert that coverage into the constructed original whole-fiber Jacobian
   socles for every original iterate, with positive actual dimension explicit.
6. Grading-preserving polynomial maps commute with actual homogeneous components;
   apply to actual invertible source linear changes and reindexing.

No complete original homogeneous relation, simultaneous Bertini fiber union,
Section 4 geometric sheaf lifting, or actual intersection inequality is claimed.
The full Linearity Theorem remains UNPROVED.
