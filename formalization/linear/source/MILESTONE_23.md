# Milestone 23: an actual affine low-degree functional

The full Linearity Theorem remains **UNPROVED**. The manuscript is unchanged.

From the proved degree-controlled ideal representation, `AffineFunctional.lean` descends a top homogeneous-component functional through the bounded-degree polynomial subspace onto the actual affine quotient. The kernel inclusion is proved using the actual highest-part ideal comparison. The construction reuses mathlib's `LinearMap.liftOfSurjective`.

For positive-degree regular highest parts with origin-only common zero locus over an algebraically closed characteristic-zero field, a functional on the actual affine quotient is constructed that vanishes on every polynomial of degree below `D=sum(deg(P_i)-1)` and takes value 1 on the determinant of the highest-part Euler coefficient matrix. No affine vanishing functional, residue, or perfect pairing is supplied as an input to this theorem.

This is a nonzero **linear functional**, not yet a claimed perfect pairing or the normalized global residue. Its normalization is on a specific highest-part determinant. The remaining comparison is to the universal difference diagonal and then to geometric residues. A low-degree vanishing functional alone does not prove the required global Euler-Jacobi relation.

Primary library discovery: https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Isomorphisms.html ; exact pinned implementation inspected at mathlib `2a885768dae569d938bb9ff3474da6a8753bb90a`. Actual build and axiom records are separate from publication.
