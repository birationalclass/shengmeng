# Checkpoint 111 discovery and scope

Online discovery inspected mathlib's Cardinal/Finite documentation
(https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Cardinal/Finite.html)
and Set/Sigma documentation. The pinned implementation supplies `Nat.card_sigma`,
`Nat.finite_of_card_ne_zero`, `Fintype.equivFinOfCardEq`,
`Equiv.sigmaSubtypeFiberEquivSubtype` and `Set.Finite.preimage'`.
Their full local types were read before adaptation. The actual source
preimage is the original point-map preimage, not an unrelated family.

The existing audited `Linear.Evaluation` supplies actual polynomial evaluation
maps and nonzero weighted functionals. A finite-subset sum is proved by the
actual subtype embedding and `Finset.sum_subset`. No surjectivity of the
geometric restriction map is silently added.

Original-entry comparison uses checkpoint 110's simultaneous good targets and
WHOLE projective fibers, checkpoint 109's actual pullback common POINT set,
and the original Hilbert-leading-coefficient equality d=degree V.

Separate online discovery for canonical sheaf, proper/Serre duality and Serre
vanishing found no applicable checked general algebraic-projective theorem in
the searched pinned sources. An analytic Riemann-surface Serre-duality axiom
was rejected: it is neither the right geometric scope nor a proved result.
This focused search does not establish absence of all implementations.

This checkpoint closes the finite-point input to Section 4. It does not close
scheme reducedness, transversality, geometric Koszul, proper duality, uniform
Serre bounds, fixed-degree Q lifting or the actual intersection inequality.
