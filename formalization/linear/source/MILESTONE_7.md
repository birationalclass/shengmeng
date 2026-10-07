# Milestone 7: actual closed specialization and regularity

The full Linearity Theorem remains unproved. The checked project now contains
182 theorem/lemma proofs, 52 definitions, and 324 audited declarations
including separately counted ports.

New verified mathematics:

1. Construct the actual augmentation of an Artinian power-series complete
   intersection. Its kernel is the coordinate ideal and the nilradical.
   Construct a normalized perfect multiplication pairing and prove that its
   algebraic trace element is the rank times the coefficient determinant.
2. Construct coefficient specialization K[[s]][[z]] -> K[[z]], prove its
   exact kernel, and identify the quotient by the equations followed by the
   parameter ideal with K[[z]]/(specialized equations).
3. Prove that formal partial derivatives and their Jacobian determinant
   commute with this specialization, including in the actual double quotient.
4. Exchange regular sequences in a Noetherian local ring. Applying flatness
   of the original equation quotient, prove that the specialized equations
   form a regular sequence. Their zero constant coefficients are derived,
   rather than assumed separately.

Every public declaration was kernel checked and its axioms audited. There
are no sorry/admit proofs or new project axioms. General helper hypotheses,
including Artinian and finite-dimensional hypotheses, remain explicit.

The coefficient determinant is not yet identified with the derivative
Jacobian. Finite-dimensionality of the actual specialized quotient must
still be derived from the original finite-flat relative algebra. Arbitrary
parameter Jacobian survival and the global geometric proof also remain open.

Discovery used the pinned mathlib power-series kernel-of-map, regular-sequence
flatness, quotient, and derivative APIs. The next bridge is the actual
quotient/tensor closed-fiber comparison; the standard mathlib quotient tensor
equivalence has been inspected before attempting its implementation.

Reproduce with build.py and audit.py. Release and browser evidence are recorded
separately after publication; this file alone asserts no deployment success.
