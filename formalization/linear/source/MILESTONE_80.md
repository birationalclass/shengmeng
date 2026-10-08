# Local checkpoint 80: actual homogeneous coordinate grading

The exact `LinearityTheoremGoal` remains **unproved**.

The degree-m component of the ORIGINAL polynomial coordinate quotient is
constructed as the image of mathlib's homogeneous polynomial submodule
under its actual quotient map. Its elements have homogeneous representatives,
and each component is finite-dimensional over the original base field.

The existing actual homogeneous quotient projections are proved to act as
the identity on their own component and as zero on every other component.
Finite homogeneous decomposition then proves independence and total span,
giving an actual mathlib internal `GradedAlgebra` of the original quotient.
Multiplication respects degree addition. No grading is supplied as an input.

The original projective coordinate-domain pullback maps the degree-m piece
to the degree-q*m piece, is injective, and commutes with the corresponding
quotient projections. Thus the actual finite-dimensional Hilbert functions
satisfy H(m) <= H(q*m).

The full local build and axiom audit pass: 1023 project theorem proofs,
196 definitions, 1415 audited declarations and 310 Lean source files.
Only propext, Classical.choice and Quot.sound occur. No sorryAx or project
custom axiom is present in the audited snapshot.

No Hilbert polynomial, growth exponent, geometric dimension or equality
D=q^dim(V) is assumed or proved here. Hilbert--Serre library reuse is being
investigated separately. Scheme gluing, Bertini sections, uniform global
duality/Serre polynomial lifting and geometric Bezout remain unfinished.
