# Milestone 12: the original relative Jacobian annihilator conclusion

The full Linearity Theorem and full Lemma31Goal remain unproved.

The root build and complete kernel audit pass: 297 project theorem proofs,
74 definitions and 461 declarations including ported declarations. Only
propext, Classical.choice and Quot.sound occur. All compiled/exported Lean
sources use LF. A Prop definition is not counted as a proof.

## Mathematical advance

Construct an actual B-algebra automorphism of B[[z]], B=K[[s]], from the
given reduction map. Its normal coordinate images in B have zero constant
coefficient, derived from the split surjective local map. Translation
z_i -> z_i-a(z_i) centers them, fixes B, commutes with normal partial
derivatives and transports the actual Jacobian determinant.

Construct an actual recursive nested-power-series ring equivalence
K[[s]][[z]] -> K[[s,z]], with parameter-coordinate and derivative
compatibilities proved by coefficient calculations. Translation uses
mathlib's substitution, continuity and polynomial density.

Transport regular equations, their quotient, finiteness, flatness and the
nilradical reduction kernel by the inverse coordinate change. Apply the
centered theorem and transport its actual determinant back. The result
finiteFlat_jacobian_annihilator has the original finite-flat regular
equation hypotheses, characteristic zero, positive dimensions and a
B-algebra reduction with nilradical kernel. There is no extra centering,
perfect-pairing or primitive-generator hypothesis.

lemma31_annihilator_conclusion proves exactly the first conjunct of
Lemma31Goal in its existing complex-field notation: Ann(N)=B Delta.

## Remaining obligations

The arbitrary-parameter-lift conjunct is unfinished: construct the actual
new parameter algebra action, finite-flat presentation and pairing, or an
equivalent direct proof, then prove nonzero socle generation. The existing
ParameterPairingChange helper explicitly assumes that new action and
pairing and does not discharge this obligation.

Scheme/projective-coordinate comparison, dimension and degree, Bertini
and generic etale fibers, global Euler-Jacobi residues, geometric Koszul,
proper duality and Serre bounds, and actual Cartier/Bezout estimates remain
open. Publication is a checkpoint; mathematical work continues afterward.

## Reuse and discovery

Inspect pinned mathlib and official docs for MvPowerSeries.Equiv, Rename,
Derivative, Substitution, LocalRing.RingHom.Basic, Ideal.Quotient.Operations,
Regular.RegularSequence and Flat.Basic before constructing new bridges.
Reuse the actual finSucc equivalence, rename equivalence, substitution
algebra homomorphism, quotient equivalence, regular-sequence transport and
module transport. The inspected APIs did not directly provide the nested
normal translation and its derivative compatibility; those bridges are
proved locally. Searches for arbitrary parameter changes found unit
inversion and analytic inverse results, which do not alone provide a
formal multivariate substitution inverse. This focused search does not
claim that no implementation exists elsewhere.

Primary documentation:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPowerSeries/Equiv.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPowerSeries/Rename.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient/Operations.html
