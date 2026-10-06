# Linearity formalization

The **global Linearity Theorem remains UNPROVED**. Its coordinate formulation `LinearityTheoremGoal : Prop` is a target definition, not a proof; comparison with the original Scheme formulation remains open.

The exact local target is now proved:

```lean
LinearStudy.lemma31_complete (r c : ℕ) : LinearStudy.Lemma31Goal r c
```

`Lemma31Goal` keeps its historical Lean name; the current manuscript labels this statement Lemma 2.1. The proof includes relative Jacobian annihilator generation and, for every allowed arbitrary parameter lift, the Artinian quotient, maximal ideal, nonzero Jacobian and socle generation. It assumes only the original regular equations, finite flatness, positive dimensions and the stated reduction/parameter generation; it constructs the new parameter action, coordinate change, finite freeness and perfect pairing.

See `MILESTONE_16.md` for the new proof chain and library provenance. Earlier `MILESTONE_*.md` files record historical partial stages; their then-open local obligations are closed by this milestone.

## Reproduce and inspect

Lean 4.35.0-rc3; pinned mathlib commit `2a885768dae569d938bb9ff3474da6a8753bb90a`. The source archive contains the lake manifest and toolchain. The local `build.py` reuses a matching read-only dependency cache; `audit.py` records every declaration, exact type, allowed axiom, compiler source interval and actual project-code dependencies.

- `Linear/LiftedParameterMaps.lean`: actual parameter coordinate and quotient maps with base automorphism compatibility.
- `Linear/LiftedParameterPresentation.lean`: regular equation presentation and proved finite free action.
- `Linear/ArbitraryParameterJacobian.lean`: constructed pairing and arbitrary-parameter Jacobian nonvanishing.
- `Linear/ArbitraryParameterSocle.lean`: socle ideal equality and full `lemma31_complete`.
- `Linear/Target.lean`: unchanged complete local statement.
- `Linear/Projective.lean`: precise global coordinate target, still unproved.

## Remaining global obligations

Scheme/coordinate comparison and dimension/degree interfaces; Bertini and general étale fibers; global Euler–Jacobi relation; geometric Koszul, proper duality and uniform Serre polynomial lifting; actual Cartier intersection and projective Bézout estimate. Numerical or local algebra helpers alone do not prove these geometric statements.

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed in audited declarations. Build, audit, source hashes and release verification remain separate records. Ordinary cards count their own declaration intervals; packs merge all member and actual project dependency intervals without double counting.

## Attributed reused sources

The three modules under `Linear/Vendor` are attributed Apache-2.0 adaptations
from mathlib PR #34913 at the commit recorded in `vendor-provenance.json`.
The PR is not part of the pinned mathlib release. Every public declaration
in the adapted modules is included in the local axiom audit. Reused proofs
are counted separately from project-owned proofs.

Unproved geometric bridges: the integral projective Scheme comparison and
dimension/degree APIs; Bertini and étale fiber counts; the complete-intersection
Jacobian/socle theorem and Euler–Jacobi relation; geometric Koszul exactness,
proper duality, Serre bounds and uniform polynomial lifting; actual Cartier
intersection and Bézout degree.

No geometric conclusion is concealed in a structure's assumption and no
`sorry`, `admit`, custom `axiom`, or imported Negativity theorem is used.
Conditional helper theorems retain their hypotheses in the exact Lean types.

## Reproduce

Pinned Lean: `leanprover/lean4:v4.35.0-rc3`.
Pinned mathlib: `2a885768dae569d938bb9ff3474da6a8753bb90a`.

```
lake update
lake exe cache get
lake build
lake env lean CheckAxioms.lean
```

The local validation used `build.py` and `audit.py` against an already installed
matching mathlib cache. It did not mutate the Negativity project or use its
mathematical declarations. Build exit codes, exact types, axiom reports and
source SHA-256 hashes are exported with this project.

The spatial proof atlas reuses the Negativity interface through its independent
Jordan Size adaptation. Its gold card identifies the current target, not a
completed proof. The full manuscript draft and private audit report are not
published; only its target, proof route and file hash are included.

## Milestone 10: actual multivariable derivative Jacobian

`JacobianNonzero.lean` proves nonvanishing and scalar socle generation of
the actual derivative Jacobian for zero-constant regular equations over
a characteristic-zero field whose actual power-series quotient is Artinian
and finite-dimensional. The pairing, equation unit change and difference
matrix are constructed. No Jacobian nonvanishing or socle identity is an input.

`DiagonalTrace.lean` constructs the actual pairing diagonal and connects its
tensor multiplication to algebraic trace. `PolynomialApproximation.lean`
constructs finite polynomial equations P=UH with U(0)=I. The universal
difference matrix has both actual derivative and coefficient specializations.
Its right augmentation is proved nonzero using the original regular equations,
forcing its trace coefficient to be a unit. This closes the field/closed-fiber
Jacobian obligation left open in the historical descriptions above.

The general relative base-ring theorem, arbitrary lifted parameters and
global geometric proof remain unproved. This milestone does not complete
`Lemma31Goal` or `LinearityTheoremGoal`.

## Milestone 11

Actual residue-tensor Jacobian nonvanishing and primitivity, centered relative annihilator generation, and survival under an explicitly supplied changed-base pairing are now checked. Coordinate translation and construction of that pairing from arbitrary parameter lifts remain open. See MILESTONE_11.md.

## Milestone 12: original relative Jacobian annihilator

Actual nested-power-series coordinate equivalences, parameter-algebra centering and normal derivative compatibility are constructed. The original finite-flat regular equation quotient now satisfies Ann(N)=B Delta without an extra centering or pairing input. lemma31_annihilator_conclusion proves the first conjunct of the existing target. The full target, arbitrary parameter-lift socle result and global Linearity Theorem remain unproved. See MILESTONE_12.md.

## Milestone 13: precise code counts and parameter linear part

Cards now count their own compiler-recorded declaration ranges; packs count all member code and actual project-code dependencies with overlapping intervals deduplicated. The header retains a separate whole-project total. The actual derivative matrix at zero of a maximal-ideal parameter generating set is proved invertible. Formal parameter inversion, new-base finite flatness, arbitrary-lift socle generation and the global theorem remain unproved. See MILESTONE_13.md.
