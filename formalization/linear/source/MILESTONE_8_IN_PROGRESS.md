# In-progress milestone 8: finite actual closed fiber

The full Linearity Theorem and general derivative-Jacobian comparison remain
unproved. The local audited snapshot contains 186 project proofs and 52
definitions (328 audited declarations including ports); the frozen GitHub
release remains milestone 7 with 182 project proofs.

FiniteSpecialization.lean now proves:

- A surjective coefficient-compatible quotient specialization is a surjective
  semilinear map. A finite module over the original base therefore has a finite
  specialized quotient over the coefficient field.
- The actual specialized power-series quotient is finite-dimensional, directly
  from finiteness of the original relative algebra. No extra fiber finiteness
  assumption is needed.
- That quotient is Artinian.
- Original regular equations and finite flatness together construct a perfect
  multiplication pairing on the actual specialized quotient, normalized at a
  coefficient determinant, and give its algebraic trace-element formula.

This uses mathlib Module.Finite.of_surjective, inspected in the pinned source
and official documentation before constructing the quotient semilinear map.

The next work is an actual residue-field tensor-product comparison, then the
general derivative-Jacobian identity. Experiments under research/ are excluded
from all proved counts and published Lean source.
