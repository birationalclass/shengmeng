# Checkpoint 100 discovery: actual projective representatives

Online primary candidate inspected:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Projectivization/Basic.html

Pinned local implementation:
Mathlib/LinearAlgebra/Projectivization/Basic.lean, Projectivization.mk_eq_mk_iff'.
Its exact statement identifies two nonzero representatives precisely by scalar
multiplication. This is reused, not postulated. The original coordinate-zero
and affine ratios are then derived from equality with the normalized point.

Existing audited project APIs reused:
- normalizedProjectivePoint_coordinate_ratios and injectivity;
- homogeneous_affine_chart_eval and affineDehomogenize_eval;
- projective_iterates_whole_fibers_homogeneous_relations from checkpoint 99.

For a representative v of (1,x), v_0 is proved nonzero and v_i/v_0=x_i.
Replacing normalized coefficients lambda by lambda/v_0^t gives the exact
homogeneous evaluation relation at v. All new coefficients stay nonzero.
The original-iterate wrapper accepts only the original geometric data and
constructs the good open and relation; it does not assume the normalized
relation as an extra original geometric hypothesis.

Scopes remain explicit: actual positive chart dimension, iterate degree >1,
whole good fibers on a constructed nonempty open, complex projective points.
Simultaneous Bertini selection, scheme comparison, Section 4 and actual
intersection are not claimed.

Private source and compiler evidence are recorded separately; public promotion
does not itself constitute a completed full-project build or audit.
