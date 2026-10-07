# Milestone 41: actual projective invariance implies ideal power bounds

For the actual HomogeneousEndomorphism and IntegralProjectiveEquations objects from the original target, projective point total invariance lifts to total invariance of the actual affine cone, including the origin. The zero locus of the actual polynomial pullback ideal is proved to be the preimage under the evaluated coordinate tuple. Pinned mathlib Nullstellensatz then proves radical(f*I)=I using the original prime ideal, not a supplied radical equality.

No surjectivity or local smooth coordinate assumption is used in this bridge, and only positive polynomial degree is required. Finite-generation of the polynomial ideal radical gives an exponent e>0 with I^e <= f*I <= I. Mapping these actual ideals along any ring map psi preserves the sandwich. This is applicable to actual localization and formal coordinate/completion maps without any extra claim that radicals commute with completion.

Discovery: read the official pinned Nullstellensatz.lean via GitHub API and its full local definitions and types. Reused its proved vanishingIdeal_zeroLocus_eq_radical and actual map-ideal/finite-generation APIs. No new axiom.

The global Linearity Theorem remains unproved; actual smooth coordinate ideal identifications, etale parameter generation and global duality/intersection steps remain.
