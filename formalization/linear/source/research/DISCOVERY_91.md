# Same actual target, linear parameters and actual coordinate diagrams

Library-first primary online discovery inspected:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/RingHom/Unramified.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Unramified/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Nakayama.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/PDeriv.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/LinearMap/Polynomial.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Basic.html

Pinned local types and the existing user modules were read before adaptation.
Reuse OriginalPolynomialNormal, PolynomialLocalParameters, SmoothTargetParameters,
PointLocalCoordinateEquiv, ProjectiveSmoothPointParameters and the actual whole
ambient fiber construction. The source and target are not replaced by abstract
independent smooth points.

The existing target-parameter theorem produced polynomials without stating
their degree. Its actual inverse linear-coordinate construction yields
centered linear polynomials. Matrix.toMvPolynomial_totalDegree_le and
MvPolynomial.totalDegree_rename_le prove degree at most one; direct evaluation
proves they vanish at the original point. Nakayama already proves they generate
the original local quotient maximal ideal. Their number is identified with the
actual quotient differential rank, and the whole-fiber aggregate uses that SAME
r for every original iterate.

The actual ambient ring-map square induces the actual quotient-local map square.
No local commutativity or new unramification condition is assumed. The pinned
RingHom.FormallyUnramified.of_surjective, comp and of_comp transport the original
unramification through constructed source/target ring equivalences.

IsLocalization.algEquivOfAlgEquiv extends the source coordinate map across the
actual transformed denominator. The actual original ideal image and rational
polynomial chart map commute with this equivalence, including invSelf.

The privately tested PolynomialNormalLinearParameters prototype is not promoted:
its normalization repeats the existing OriginalPolynomialNormal route. The
promoted construction reuses that existing proof instead.

The actual same-fiber common Jacobian socle, full homogeneous relation, Bertini
d-target/fiber union, Section 4 uniform geometric lifting and actual intersection
are still open. Exact private source/log provenance is recorded separately.
