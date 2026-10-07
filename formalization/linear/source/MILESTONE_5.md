# Milestone 5: Koszul foundations for the multivariable socle step

The full Linearity Theorem remains unproved. This is a checked intermediate
foundation release, not a completed Jacobian or geometry theorem.

Commit: `143fde1b208fa3cd10bd4244ae11d111f1908db7`.

The released snapshot contains 143 project-owned theorem/lemma proofs and
40 project-owned definitions. All public declarations in the three adapted
vendor modules are audited separately; their counts are recorded as
`reusedTheoremCount` and `reusedDefinitionCount` in `snapshot.json`.
Only standard Lean axioms are used, with no `sorryAx` or custom axioms.

New proved mathematics:

1. The complete list of variables of a finite-variable power-series ring
   over any nontrivial commutative ring is a regular sequence.
2. The augmented Koszul complex of a regular sequence is an actual projective
   resolution of its quotient, using free exterior powers and a proved
   quasi-isomorphism. Exactness of its augmentation is proved directly.
3. The highest exterior power of `R^n` is linearly equivalent to `R`;
   the induced map of an endomorphism multiplies by its determinant.
4. An equation `H = M x` gives an actual chain map `K(H) → K(x)`, whose
   top component is multiplication by `det M`.
5. Two homotopic endomorphisms of `K(H)` have top coordinates congruent
   modulo the equation ideal `(H)`.

The Koszul complex/exterior-power dependency was discovered in mathlib
PR #34913. Its relevant original modules were inspected, minimally adapted
to the pinned Lean/mathlib version, compiled, and axiom audited.
The PR is not merged into this project's pinned mathlib release.
Original authorship and Apache-2.0 headers are preserved. Source URLs,
upstream commit, original/adapted hashes and declaration manifests are in
`vendor-provenance.json`. Downloaded experiments are excluded from the
published source archive and declaration counts.

The nonzero socle-generator theorem still needs to connect a socle element
to a lifted comparison of these resolutions. Identification of the actual
derivative Jacobian, its survival under arbitrary parameter lifts, and all
global geometric bridges also remain open.

Verification: local Lean root build, public-declaration axiom audit, exported
source/zip/Git-blob equality, bilingual card/source inspection, GitHub Lean
build and Pages deployment all succeeded. All 36 checked deployed assets
agree with their committed Git blobs. See `live-validation.json`.
