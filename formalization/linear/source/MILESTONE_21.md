# Milestone 21: actual affine highest-part reduction

The full Linearity Theorem remains **UNPROVED**. The original manuscript is unchanged.

`AffineFiltered.lean` works with actual multivariate polynomial ideals and quotient rings. It proves, rather than assumes:

- A homogeneous ideal element of degree n has a representation with homogeneous coefficient of degree n-deg(P_i), and coefficient zero when deg(P_i)>n.
- Subtracting the highest homogeneous component strictly lowers degree.
- Finite polynomial quotients have bounded-degree representatives. In a finite homogeneous quotient, all sufficiently large homogeneous degrees vanish.
- If the highest homogeneous parts of arbitrary affine equations have common zero locus exactly the origin, their actual affine quotient is finite-dimensional. Regularity of the highest parts is not required for this finiteness result.
- Over an algebraically closed characteristic-zero field, if the n+1 highest parts have positive degrees and are regular, with origin-only zero locus, every class in the actual n+1-variable affine quotient has a polynomial representative of degree at most D=sum(deg(P_i)-1).

The homogeneous perfect pairing from milestone 20 proves the precise top-degree bound D; the affine theorem uses that bound and iterated strict degree reduction. There is no supplied normal-form or finite-quotient input in the final affine theorems.

This normal-form bound does **not** imply that the normalized affine residue functional vanishes below D. The remaining comparison must control leading cancellation in affine ideal relations, or construct the equivalent filtered/graded complete-intersection comparison. A different normalized local functional must not be substituted for the global residue. Koszul first-syzygy control is the next targeted bridge. The geometric, Serre/duality and projective intersection obligations also remain open.

Lean 4.35.0-rc3; pinned mathlib 2a885768dae569d938bb9ff3474da6a8753bb90a. Build and axiom-audit records are separate from GitHub deployment records.
