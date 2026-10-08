# Checkpoint 96 library discovery and scope

Primary online sources checked during original whole-fiber assembly:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Artinian/Module.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient/Operations.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPolynomial/Homogeneous.html

The pinned local implementations and full types of `IsArtinianRing.of_finite`,
`Ideal.Quotient.liftₐ`, `Ideal.quotientEquivAlgOfEq`, `Ideal.Quotient.algHom_ext`,
polynomial renaming equivalences and algebra equivalence composition were
inspected. These standard constructions were reused, together with already
audited actual source/target coordinate and original local-map modules.
The sources did not themselves supply the original manuscript-specific
whole-fiber normal-Jacobian assembly. The missing bridge was proved locally;
no downloaded setup code or new axiom was used.

The actual source polynomial coordinate equivalence and independent target
linear combinations preserve the full ambient equation ideal and finiteness,
including normal nilpotents. Actual source points, evaluations and original
local generators are transported into the exact point primes used by the
rational local map. Its centered target-origin comparison derives numerator
vanishing and actual quotient evaluation, rather than assuming them.

For every original iterate the previously constructed whole-fiber common
source presentation and centered target normal presentation are inserted.
The resulting SAME polynomial normal Jacobian generates a nonzero socle at
EVERY actual source point. Positive actual chart dimension is explicit.

This does not yet prove the original homogeneous relation: maximal-ideal
coverage, transformed leading-form regularity, residue degree bounds and
the original homogeneous conversion still require assembly. Bertini union,
global Proj comparison, Section 4 and actual intersection remain open.

Exact private compiler source hashes and successful logs are recorded in
`checkpoint96-private-provenance.json`. Full public compilation and axiom
audit are required before this checkpoint counts as verified.
