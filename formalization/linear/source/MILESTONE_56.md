# Milestone 56: actual smooth points construct common formal coordinates

The global Linearity Theorem remains unproved.

Nine new project theorem proofs:

- Localization of a domain preserves the rank of its actual differential module.
- The localized polynomial quotient has the same differential rank as the original prime quotient.
- At a smooth point, conormal rank is the ambient variable count minus that fixed rank.
- For a nonzero prime ideal this common conormal rank is positive.
- Finitely many rational smooth points admit one actual invertible ambient polynomial change and actual formal maps taking the ORIGINAL ideal to the normal-variable ideal. Neither a common conormal rank nor chosen normal columns are additional inputs.
- The library predicate `Algebra.IsSmoothAt` on the prime quotient is transferred through the actual quotient-localization equivalence and used to construct those coordinates.

The domain/prime hypotheses and rationality/smoothness of the chosen finite nonempty point family are explicit. No smoothness of the whole, potentially singular variety is assumed. This is not yet Bertini, generic smoothness, or a projective-fiber construction.

The remaining proof chain requires actual general smooth/etale fibers, the projective chart/formal pullback comparison and parameter generation, geometric dimension comparison, uniform Serre/duality polynomial lifting, and actual Cartier/Bezout intersection numbers. All remain open where indicated in the atlas.
