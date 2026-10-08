# Hilbert--Serre for the actual coordinate quotient

Reuse source: mathlib PR 9819, commit
413e5b872a7c758e0eb91f99cb96d6a61c81f0a2:
https://github.com/leanprover-community/mathlib4/pull/9819
Inspected upstream files and SHA manifests remain in upstream-hilbert9819-source.
Apache headers are preserved in adapted files. The pinned mathlib cache is unchanged.

Rather than porting the old grade-zero-ring scalar transport wholesale, the
proof is specialized to a fixed base field K and degree-one generators, exactly
as required by a polynomial coordinate quotient. The induction route is reused:
remove one homogeneous generator x; its kernel and cokernel are annihilated by x,
so finite generators still work over the actual smaller adjoined algebra.
Actual internal decompositions, actual degreewise multiplication maps and their
exactness give rank-nullity and the generating-series recurrence. Induction
produces a polynomial numerator with denominator (1-X)^s.card.

Existing pinned mathlib APIs are reused for homogeneous Subsemiring closures,
adjoin induction, Noetherian finite modules, quotient actions, DirectSum internal
criteria, linear rank-nullity, PowerSeries coefficients and truncation, and
Polynomial.existsUnique_hilbertPoly. The older additive-function category port
is retained privately but is not needed by this field-specialized proof.

The actual original quotient grading and finite degree pieces from checkpoint80
are used, and the actual images of polynomial variables supply its generators.
This derives an eventual unique rational Hilbert polynomial from I. No growth
polynomial, geometric dimension or function-field degree value is supplied.

Still missing: Hilbert polynomial growth degree versus geometric dimension,
the degree comparison giving D=q^dim(V), Scheme gluing, Bertini sections,
proper duality/Serre uniform polynomial lifting and geometric Bezout.
