# Same-target normal equations and actual rational coordinate changes

Continue the primary online/pinned-source discovery recorded in DISCOVERY_91:
mathlib RingHom.Unramified, MvPolynomial.Eval, MvPolynomial.Homogeneous,
LinearMap.Polynomial and Localization.Basic. Further primary documentation:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Eval.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/LinearMap/Polynomial.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/RingHom/Unramified.html

Read actual pinned local declarations and reuse OriginalPolynomialNormal,
FirstJetNormalForm, PolynomialFormalDerivative, PolynomialLocalParameters,
HomogeneousRationalPullback and PointLocalPullbackCoordinateComparison.
No downloaded setup script or new mathematical axiom is used.

The same actual original smooth target now supplies polynomial normal equations
in constructed invertible linear coordinates. Their number is c=n-r, using the
SAME original chart Krull/differential dimension r. Their formal first jets are
the normal variables modulo the actual maximal-ideal square. They generate the
completed image of the ORIGINAL ideal, not an independent ideal. The whole
original iterate fiber aggregate retains these same-target equations along with
its previously checked common source coordinates and linear parameters.

Actual rational source coordinate equivalences preserve the original localized
quotient map's unramification, constructing transformed primes and ideal
compatibility from the original map. Actual linear target coordinates transform
the original numerators and preserve genuine local unramification. Affine
target centering adds the unchanged denominator times the translation constant.
The actual ring-map equalities are proved by polynomial evaluation and the
existing homogeneous scaling identity; no new diagram is assumed.

These source/target coordinate results are still to be assembled with the SAME
ambient common Jacobian socle. The original full homogeneous relation, Bertini
d-target/fiber union, global Proj comparison, Section 4 geometric lifting and
actual intersection inequality remain open. The final theorem remains unproved.
