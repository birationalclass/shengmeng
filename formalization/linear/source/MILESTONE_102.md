# Checkpoint 102: original linear projection without basepoints

The full Linearity Theorem remains UNPROVED.

Original V now has r+1 actual degree-one forms defining an injective finite cone map and no projective basepoint. The actual Hilbert-polynomial degree and affine-chart Krull dimension determine r. Exact generic section cardinality d, simultaneous Bertini, Section 4 and actual intersection remain open.

Full project build and standard-axiom audit passed at 2026-10-09T03:28:41+08:00: 1315 proofs, 250 definitions, 1761 declarations, 436 Lean files.

Actual entry: LinearStudy.projective_exists_linear_normalization_chart_dimension in Linear/ProjectiveLinearNormalization.lean.
The forms, finite map, dimension and no-basepoint conclusion are constructed from the original V; no basepoint-free tuple or finite map is assumed. A monic integral equation evaluated on all scalar multiples proves the no-basepoint conclusion.

Hilbert-polynomial degree r is the dimension. This does not identify the leading coefficient (degree V = d) with generic linear-section cardinality. That bridge and simultaneous avoidance of bad loci remain open.
