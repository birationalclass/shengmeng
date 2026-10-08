# Discovery 101: genuine degree-one normalization

Target: construct a linear projection for the original simultaneous
Bertini setup. A nonlinear affine normalization cannot be substituted for
the degree-one linear forms used by the manuscript.

Official sources inspected online and in the pinned local mathlib:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/NoetherNormalization.html
  supplies the quotient-integrality and kernel induction pattern. Its
  Nagata coordinate changes contain high powers, and do not preserve
  the original degree-one linear forms. The induction and quotient
  construction are adapted with Apache-2.0 attribution.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPolynomial/Homogeneous.html
  supplies finite homogeneous decomposition, homogeneous components,
  evaluation over an infinite field and homogeneous rename operations.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Equiv.html
  supplies the actual finSuccEquiv for monic elimination.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/GradedAlgebra/Homogeneous/Ideal.html
  supplies the genuine homogeneous ideal predicate; the recursive kernel
  property is proved using the actual degree-preserving map.

Focused online searches did not locate a matching reusable degree-one
normalization proof. This does not assert that no such code exists elsewhere.
Pinned mathlib: 2a885768dae569d938bb9ff3474da6a8753bb90a;
Lean 4.35.0-rc3. Only the inspected compatible declarations are reused.

New uncovered bridge:
1. construct invertible linear shear, with actual inverse and preserved degree;
2. obtain nonzero constant leading coefficient of a homogeneous original equation;
3. construct integral deletion map through actual quotient equivalences;
4. prove its kernel homogeneous, then perform the genuine linear induction;
5. prove module-finiteness and equality with the actual Krull dimension.

Scope: proper homogeneous ideal over an infinite field. No assumed
linear normalization, integral map, finite map or chosen dimension.
This does NOT yet prove exact projective section degree, simultaneous
Bertini smooth target points, Section 4 or the final Linearity Theorem.
See checkpoint101-private-provenance.json for exact checked source hashes
and independent compile/axiom logs; a full-project audit is separately required.
