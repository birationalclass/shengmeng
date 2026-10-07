# Milestone 20: homogeneous low-degree vanishing on an actual quotient

The full Linearity Theorem remains **UNPROVED**. The manuscript is unchanged.

`HomogeneousQuotient.lean` proves the following precise foundation. Let K be an algebraically closed field of characteristic zero. Let P be n+1 homogeneous regular equations in n+1 variables, of positive degrees e_i, whose common K-zero locus is exactly the origin. Set Q=K[X]/(P), D=sum(e_i-1), and M_ij=(1/e_i) partial_j P_i.

There is an actual perfect multiplication pairing on Q whose functional sends the class of det M to 1 and vanishes on the class of every polynomial of total degree less than D.

The construction proves quotient finiteness by the actual Nullstellensatz, descends the homogeneous-component projection to Q, applies Euler's derivative identity to the coefficient determinant, proves this determinant's nonzero socle class, identifies every maximal ideal with the origin reduction kernel, and applies the proved global Artinian-socle detection theorem. None of the pairing, low-degree vanishing, determinant nonvanishing or socle identity is supplied as an input.

This is the homogeneous, origin-supported case. It is not the general affine Euler-Jacobi theorem, and it is not a comparison with geometric Grothendieck residues. The next obligation is highest-homogeneous-part/filtered comparison for the original affine equations. The other original geometric, Serre/duality and intersection obligations remain open.

Pinned toolchain: Lean 4.35.0-rc3, mathlib 2a885768dae569d938bb9ff3474da6a8753bb90a. Full build and declaration axiom audit are recorded separately; a compiled target definition is not counted as a proof.
