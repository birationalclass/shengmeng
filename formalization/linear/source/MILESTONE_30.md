# Milestone 30: ambient completion comparison for actual local fibers

The full Linearity Theorem remains **UNPROVED**. The manuscript is unchanged.

The actual completion evaluation map has kernel equal to the extension of the corresponding ideal power. If `I^n ≤ J`, factoring that evaluation to `R/J` gives a surjective algebra map with kernel exactly the extension of `J`. Thus the completion modulo that extension is algebra-isomorphic to `R/J`. The proof constructs this comparison; no such isomorphism is assumed. For a Noetherian local ring with Artinian `R/J`, mathlib derives the required maximal-ideal power containment.

For an actual prime ideal of `R/I`, the source localization `R_P/I R_P` is identified with `(R/I)_p` using mathlib's quotient-localization instance and the actual surjective image of the prime-complement monoid. Combining this with ambient completion identifies the completed ambient fiber quotient with the actual localized fiber. Both comparisons have explicit formulas for the image of each original coordinate-ring element. Nilradical-annihilator generation by a specified element therefore descends from the completed ambient quotient to the actual local fiber.

These are ten new project proofs and five actual constructions. They do not construct the remaining smooth/formal coordinate presentation, nor identify the manuscript's polynomial Theta with the relative Jacobian in that presentation. Those are the next obligations. Uniform proper-duality/Serre lifting and the other original global geometric inputs remain unproved.

Library-first discovery: official `Mathlib/RingTheory/AdicCompletion/Exactness`, `/Algebra`, `/Completeness`, `Mathlib/RingTheory/LocalRing/Quotient`, and `Mathlib/RingTheory/Localization/Ideal` documentation and their pinned sources. The proof reuses `pow_smul_top_eq_ker_eval`, `evalₐ`, `Ideal.quotientKerAlgEquivOfSurjective`, `exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`, the actual quotient-localization instance, `map_primeCompl_comap_of_surjective`, `IsLocalization.algEquiv`, and previously audited nilradical-annihilator transport. No new external library port is needed.

The last verified deployed version remains milestone 18; publication remains subject to the outstanding retry response. This checkpoint is local until separately audited and deployed.
