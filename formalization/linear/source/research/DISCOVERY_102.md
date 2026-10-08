# Discovery 102: actual original linear projection without base points

Original obligation: turn the genuine linear normalization into actual
degree-one forms on the original V, with no nonzero common zero and
the same actual dimension as the manuscript chart.

Library-first discovery continued online; sources inspected:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Roots.html
  Polynomial.zero_of_eval_zero is reused over an infinite field.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Eval/Coeff.html
  Polynomial.hom_eval2 transports the actual monic integral equation
  through each genuine quotient point-evaluation map.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/NoetherNormalization.html
  Existing integral-map definitions and finite-map results are reused;
  no base-point-free tuple is assumed.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.html
  Proj/basic-open APIs exist, but merely importing them does not prove
  the missing global scheme comparison or generic degree assertion.

Focused searches did not find a directly reusable original homogeneous
normalization basepoint bridge. Pinned local definitions/types were read
before adding the uncovered proof. Current live documentation can use a
newer Lean release; compilation is against the pinned 4.35.0-rc3 project.

New proof: if an original nonzero cone vector annihilated every linear
form, all its scalar multiples would lie over the same zero base point.
An actual monic integral equation, evaluated on those multiples, would
be a nonzero monic polynomial vanishing at every field element. Infinite
field polynomial extensionality excludes this.

The original V wrapper constructs the tuple and its actual induced map,
derives injectivity/finiteness/no-basepoint, and identifies r using both
the actual homogeneous Hilbert polynomial degree and affine-chart Krull
dimension. The Hilbert polynomial's DEGREE is r (dimension), not degree V.

Not claimed: the generic linear section has exactly degree V points,
simultaneous Bertini target selection, scheme comparison, Section 4 or
the final theorem. Private exact hashes/compile logs are recorded in
checkpoint102-private-provenance.json; full audit is required separately.
