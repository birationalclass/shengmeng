# Original-f native chart pullback and scheme-defining ideals

Library-first discovery used official mathlib4 documentation:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Subring/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Equiv.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/AffineScheme.html

Exact pinned local sources were inspected at mathlib
2a885768dae569d938bb9ff3474da6a8753bb90a:
HomogeneousLocalization.Away.mk and its localization formula;
RingEquiv.ofBijective, subringCongr and apply_symm_apply;
Proj.basicOpenIsoSpec, Scheme.Spec, morphismRestrict and its IsIso instance;
basicOpenIsoSpecAway; Ideal.map_span, span_le and mem_map_of_mem.

Reuse the existing original-f projectiveChartOpenMap and its original
homogeneous quotient ideal; homogeneous_aeval_smul and the actual affine
dehomogenization map. Native Proj maps requiring a degree-preserving graded
homomorphism cannot be used directly for degree-q substitution without a
grading bridge. An arbitrary chosen chart ring equivalence alone would not
justify that it represents the original coordinate pullback.

New uncovered bridge: strengthen checkpoint 114's actual chart equivalence
by retaining its compatibility with the SAME original cone fraction embedding.
The canonical equivalence sends dehomogenized H to the actual native fraction
H/X0^m. Derive the original-f substitution formula H(f0,...,fn)/f0^m.
Use the native chart isomorphism and localization of its denominator to
construct an actual morphism on an open subscheme of the original native
chart. Prove the native Spec comparison diagram commutes. Pullback of every
homogeneous family ideal is exactly the ideal of the actual substituted
equations: the denominator powers are units. This equality preserves
nilpotents and is not just a radical/point-set comparison.

Scope: complex original integral V, original positive-degree surjective f
with total-invariance hypothesis, inhabited first-coordinate chart. All
chart gluing, coverage of the projective common-zero scheme, transversality,
geometric Koszul, canonical/duality/Serre uniform Q lifting and actual
intersection remain open. No claim that current Lemma 4.1, Lemma 4.2 or
the full Linearity Theorem is proved.

Successful private exact-byte Lean builds and standard-axiom outputs:
log-native-chart-compatible4.log and log-native-chart-pullback5.log.
Diagnostic print commands are omitted from public source; public modules
must separately pass the full project build and audit before freezing.
