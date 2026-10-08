# Ambient fiber and residue-algebra boundary

Online library-first searches inspected the official primary documentation:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Nullstellensatz.html
The actual theorem `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` is reused
in the pinned version, with finite variables and the algebraically closed
coefficient field checked. Also read the user's ProjectiveAffineFiberFinite,
ProjectiveAffineFiberPointEquiv, ProjectiveIdealInvariance, ProjectiveChart,
AffineOriginRelation and PolynomialFiniteZeroLocus modules.

The previously constructed reduced fiber ring is the quotient INSIDE V by
its ideal plus the fiber equations. The paper's residue algebra is the AMBIENT
polynomial quotient by the fiber equations alone. It may contain normal
nilpotents. Reusing reducedness for that ambient ring would be incorrect.

Construct the actual ambient fiber ideal from the ORIGINAL forms f_i-y_i f_0.
No-base-point implies a nonzero denominator and the actual projective fiber
equation. Total invariance gives equality of its points with the in-V fiber.
The original map's finite point fibers prove this ambient quotient finite
dimensional even with nilpotents. Nullstellensatz identifies the radicals,
without replacing equality of radicals by equality of ideals or ring quotients.

The leading-form obligation was then closed using the official primary
documentation and pinned sources:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Regular/RegularSequence.html
`RingTheory.Sequence.isRegular_cons_iff` and `IsSMulRegular.not_zero` show that
the members of the regular leading sequence cannot vanish. The existing checked
`homogeneous_origin_regular` theorem applies because the actual homogeneous
fiber forms have no points at infinity. Their exact degree q is derived; no
nonzero-leading-coefficient assumption is retained. The user's already checked
`affineChartPolynomialMap_eq_dehomogenize` connects the actual chart polynomial
map to dehomogenization without rebuilding this comparison.

The final aggregate uses the SAME original whole good fiber and retains its
actual smooth/unramified good-locus predicate. Ambient quotient finiteness,
point-set/radical comparison and the exact-degree regular-leading-form system
are constructed for every original iterate. This is one whole general fiber,
not yet Bertini's d target points or the union of their fibers.

Public full build and full declaration/axiom audit passed. Exact private source
hashes and compiler logs are recorded in checkpoint90-private-provenance.json.
The next substantive task remains the SAME ambient algebra's common Jacobian
socle and full homogeneous residue relation. These are not claimed here.
