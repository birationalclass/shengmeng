# Milestone 31: constructed formal coordinates for the polynomial origin

The full Linearity Theorem remains **UNPROVED**. The manuscript is unchanged.

The completion of a commutative ring at a maximal ideal and the maximal-ideal completion of its actual localization are now identified by a constructed ring isomorphism. The forward and backward maps come from mathlib's actual isomorphisms on every ideal-power quotient. Their transition compatibility and inverse identities are proved, including the formula sending the original ring element to its localized element in the other completion. There is no supplied completion isomorphism.

For multivariate polynomials over a field, the variable ideal is proved to be the kernel of constant-coefficient evaluation and hence maximal. Combining the constructed completion-localization isomorphism with mathlib's actual `MvPowerSeries.toAdicCompletionAlgEquiv` identifies the formal power-series ring with the completion of the actual polynomial origin local ring. The polynomial-image formula is proved. The variable set can be any finite type; no algebraic-closure or characteristic-zero assumption is added to this coordinate comparison.

These eleven project proofs and four constructions are an intermediate coordinate bridge. Arbitrary closed-point recentering, smooth-subvariety coordinates, compatibility with the relative Jacobian, Bertini/generic-fiber geometry, uniform duality lifting and the original global target remain open.

Primary library discovery: official `Mathlib/RingTheory/Localization/AtPrime/Basic` documentation and pinned `equivQuotMaximalIdealPow`; official `Mathlib/RingTheory/MvPowerSeries/Equiv` and pinned `toAdicCompletionAlgEquiv`; actual `AdicCompletion.liftRingHom`, `evalₐ_liftRingHom`, `ext_evalₐ` and Cauchy-sequence quotient compatibility. No new external port was required.

Publication status remains separate: last verified deployed checkpoint 18; later local proofs are not claimed as deployed.
