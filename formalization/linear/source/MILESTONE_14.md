# Arbitrary formal parameter automorphisms

The full Linearity Theorem and the full `Lemma31Goal` remain unproved.

Over a field K, a finite nonempty family T with as many members as the variables, generating the maximal ideal of the actual ring K[[s]], defines an actual K-algebra automorphism by substitution X_i ↦ T_i. No formal inverse or inverse-function theorem is supplied as an assumption. Its inverse sends T_i to X_i. In a positive finite number of variables, the family T is therefore a regular sequence.

The proof uses the pinned mathlib instance `MvPowerSeries.instIsAdicCompleteSpanRangeXOfFinite` and `surjective_of_mk_map_comp_surjective`: substitution maps the variable ideal onto itself; constants show surjectivity on the residue quotient; completeness lifts this to surjectivity. The uncovered injectivity bridge is proved using stabilization of the ascending chain of kernels of iterates in a Noetherian ring. The module-linear result in `Mathlib.RingTheory.Noetherian.Orzech` does not directly apply to a nonlinear ring endomorphism, so no false linearity assumption is introduced.

Discovery sources, inspected alongside the version-pinned local definitions:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/AdicCompletion/Functoriality.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPowerSeries/Substitution.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian/Orzech.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian/Defs.html

Next dependency: build the new parameter action from arbitrary lifts in the thickened equation quotient, establish its finite freeness, construct its perfect pairing, and invoke the already verified pairing-change survival theorem. A compatible finite-generation theorem was located in `Mathlib.RingTheory.Finiteness.NilpotentKer`; `Mathlib.RingTheory.Regular.Free` supplies freeness ascent through an individual regular element. Neither discovery by itself proves the missing whole bridge.

Also compiled: nilpotent perturbation preserves injectivity of scalar multiplication on any module; in a local Noetherian ring and a finite module, a regular sequence stays regular after componentwise nilpotent perturbations, provided both sequences lie in the maximal ideal. The proof moves one element to the end of the sequence, applies the scalar result on the quotient by the unchanged other elements, and transports regularity back. This is an actual bridge for the arbitrary lifted parameters, not the missing finite-freeness conclusion itself.

The manuscript is unchanged. Compiled declarations, full types, source ranges, hashes and axioms are recorded in the current audit; publication status is recorded separately.
