# Checkpoint 89 discovery: one original whole fiber and its local geometry

Focused online searches for a reusable implementation of projective whole
smooth/unramified fibers with degree and local coordinates did not locate a
directly applicable complete theorem. Official sources inspected:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Spectrum/Prime/Topology.html
  `PrimeSpectrum.basicOpen_mul`: intersections of actual principal opens.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Smooth/Locus.html
  Actual smooth locus and localization comparison.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Unramified/Locus.html
  Actual unramified locus and local ring semantics.

Read the pinned basic-open product and prime ideal product results. Reused the
project's original-map whole reduced fiber construction, actual Hilbert/Krull/
differential dimension proof, original iterates, original coordinate point
evaluation, actual projective/affine fiber equation comparisons, and smooth
localization comparison. No downloaded setup scripts or unrelated libraries
are used.

The new bridge intersects the actual good-locus and cardinality opens by their
product, constructs an actual point avoiding it, and preserves all whole-fiber
properties for the same original iterate and the same actual dimension. Another
bridge identifies the actual rational point prime by coordinate evaluation and
transfers source/image smoothness and unramification to EVERY actual point of
that same whole fiber. This is Section 1 Setup to Section 3 local geometry; it
does not by itself prove the full homogeneous relation or Section 4 lifting.

The next assembly applies the existing original-ideal smooth cotangent rank,
generic common normal minor, actual polynomial coordinate automorphism and
formal-ideal comparison to this SAME complete fiber. It identifies r with
actual chart Krull/differential dimension and c=n-r. Local generators are
retained alongside the formal identity, so later socle work can use them.
The explicit output propositions contain actual equation sets and maps;
neither is an assumed structure holding the final conclusion.

A first attempt at one large dependent output type exhausted elaboration
heartbeats. It was replaced with a reusable explicit normal-presentation
proposition and scoped transparency settings; no mathematical hypothesis was
added, and all final private checks used exact source hashes with exit zero.

Reducedness here is for the actual fiber quotient INSIDE V. The AMBIENT fiber
can retain normal nilpotents, precisely the structure needed for the relative
Jacobian argument. No ambient reducedness is claimed.

Private checks are not a public checkpoint until compilation, complete types
and the full project axiom audit have succeeded.
