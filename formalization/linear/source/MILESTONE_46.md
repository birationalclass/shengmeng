# Milestone 46: original projective invariance to actual local structure

Actual polynomial variable relabeling is proved compatible with polynomial pullback, and its ring equivalence transports the radical equality derived from the original projective total-invariance condition.

For source and target point-local polynomial presentations, the actual source smooth formal map and actual target pulled-back equations now derive the formal normal-ideal radical equality. Consequently, regularity, module finiteness and module freeness follow, with no extra formal ideal-identification, regularity or flatness assumption.

The original `HomogeneousEndomorphism` and `IntegralProjectiveEquations`, with their actual invariant projective zero set, are used directly. The corresponding local relative Jacobian has a proved nonzero socle class on every admissible parameter quotient. The local parameter-generation hypothesis is still explicit; the next bridge concerns the actual etale map. Existence of point-local smooth presentations from geometric smoothness and the global uniform lifting remain unfinished. The global Linearity Theorem remains unproved.

Online pinned mathlib sources `MvPolynomial/Rename.lean` and `Ideal/Maps.lean` were read and recorded in `research/relabel-discovery.json`. Reuses actual renameEquiv, ring maps, map_radical_of_surjective, localization and completion comparisons, and the audited relative Jacobian theorem. No new axioms.
