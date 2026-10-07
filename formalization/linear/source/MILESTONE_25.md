# Milestone 25: actual weighted point evaluation

The full Linearity Theorem remains **UNPROVED**. The manuscript is unchanged.

For an Artinian algebra, actual maximal residue maps with their prescribed kernels give a surjective evaluation map to the finite product of fields. Surjectivity is proved by the actual mathlib Chinese remainder theorem; its kernel is proved equal to the nilradical. Selectors for individual points are constructed.

If `theta` generates the annihilator of that nilradical, a perfect multiplication functional applied to `a*theta` is a weighted sum of the actual maximal point evaluations of `a`. Every weight is proved nonzero. This is derived from the actual selector decomposition, nonzero maximal socles and nondegeneracy, not assumed as a formula.

The `theta` socle-generation hypothesis is explicit. It has not yet been proved for the manuscript's relative Jacobian on the actual geometric fiber. Consequently this algebraic point formula alone is not the geometric homogeneous relation of the manuscript.

Library-first discovery: official mathlib documentation `Mathlib/RingTheory/Artinian/Module.html` and pinned local `Ideal/Quotient/Operations.lean`. The actual declarations reused are `Ideal.pi_quotient_surjective` and `IsArtinianRing.nilradical_eq_iInf`.
