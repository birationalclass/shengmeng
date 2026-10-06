# Milestone 19: nondegenerate global diagonal and degree control

The full Linearity Theorem remains **UNPROVED**. The authoritative manuscript is unchanged.

Pinned Lean 4.35.0-rc3 and mathlib 2a885768dae569d938bb9ff3474da6a8753bb90a.

## New proved bridges

`PolynomialDoubleFiber.lean` constructs one universal matrix in two independent sets of polynomial variables, then maps it to the actual finite polynomial quotient tensor square. At every residue map to the field, its determinant reduces to a centered-coordinate coefficient determinant. The existing regular-sequence Koszul theorem and Artinian maximal-socle argument prove this reduction nonzero. Thus nondegeneracy is a conclusion, not an added input.

For an actual finite polynomial regular complete intersection over an infinite algebraically closed field, this constructs a normalized perfect multiplication pairing with

`p(a * det(partial_j P_i)) = Algebra.trace K Q a`.

It also constructs an actual diagonal tensor with the correct Jacobian multiplication image and a **unique** linear functional normalized by contraction on that **chosen** tensor.

`PolynomialDifferenceDegree.lean` constructs difference coefficients of degree at most `totalDegree P - 1`, including the zero-degree case. The full matrix determinant has degree at most the sum of row bounds. This is a genuine degree statement, not an assumed filtration conclusion.

`PolynomialOriginFinite.lean` uses mathlib's actual Nullstellensatz and nilpotent-kernel finiteness to prove the polynomial quotient finite-dimensional when its zero locus is exactly the origin. No regular sequence is required for this finiteness result.

## Remaining scope

The normalized functional has not been identified with the globally compatible Grothendieck residue. Independence from a different choice of difference matrix is not claimed. The degree bound by itself does **not** prove low-degree Euler–Jacobi vanishing. The no-common-nonzero-zero condition on highest homogeneous parts still requires filtered/homogeneous comparison with the original affine quotient. All geometric comparison, Serre/duality lifting and projective intersection obligations remain open.
