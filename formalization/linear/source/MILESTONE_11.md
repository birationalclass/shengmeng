# Milestone 11: actual relative Jacobian after centering

The full Linearity Theorem and the full relative Jacobian lemma remain unproved.

251 project theorem proofs and 63 definitions were compiled and audited. All 404 declarations, including imported vendor declarations, use only recorded standard Lean axioms; no sorryAx or new project axiom is present. Sources use LF before build and hashing.

- From the original finite flat regular power-series equation quotient, derive nonvanishing of the actual Jacobian in the actual residue tensor, its primitivity, and scalar socle generation in that closed fiber. No closed-fiber regularity, finite-dimensionality, or nonzero Jacobian input is used.
- Generalize the tensor diagonal comparison to a commutative base. Under explicit nilpotent coordinate and perfect-pairing hypotheses, construct the derivative determinant's trace-multiple identity and its nilradical annihilation.
- Derive Ann(N)=BΔ for the original relative finite flat regular quotient under the explicit centering condition a([z_i])=0. The perfect pairing and primitive Jacobian are derived. The coordinate centering transformation is still required to obtain the unrestricted statement.
- Prove that compatible changes of actual parameter-base actions preserve the annihilator action. An old scalar generator has unit coefficient under an explicitly supplied new-base perfect pairing and survives a quotient by parameters from a proper new-base ideal. Constructing that new action, finite flatness, and pairing from arbitrary parameter lifts remains unfinished.

Remaining obligations: coordinate translation, the new parameter-base construction, arbitrary parameter-lift socle comparison, and the global geometry/residue/duality/intersection steps. The research-only flattening construction is not counted in this published audit.

Primary library discovery: mathlib Kaehler.Basic, Trace.Basic, MvPowerSeries.Equiv, MvPowerSeries.Rename and Substitution. Exact pinned APIs and mathematical scopes were inspected before adaptation.
