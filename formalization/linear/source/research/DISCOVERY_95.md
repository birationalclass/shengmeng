# Original whole-fiber centered rational local inputs

Primary online library discovery inspected these official mathlib sources:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Rename.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Eval.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Equiv.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Span.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Artinian/Module.html

The pinned local Ideal.Maps and Localization.Basic types were inspected,
including the explicit map argument to comap_injective_of_surjective and
localization algHom_ext. Existing verified source/target coordinate,
point-local comparison, original total invariance and original whole-fiber
good-locus modules were reused. No retrieved code or setup scripts were run.

New proof bridges construct polynomial and denominator-open evaluation at
the actual changed source point. Independent source coordinates and target
reindexing derive actual map squares, ideal-power transport and original
local unramification. Original total invariance supplies both inequalities,
rather than supplying them as new assumptions.

For EVERY original source point of the SAME original whole good fiber,
derive the actual local quotient map, its SAME target prime, and its
unramification. Actual target reindexing, linear normalization and centering
take that same target prime to the origin. These constructions assemble the
actual centered rational local inputs on the whole original good fiber.

The original common source normal generators, centered target generators,
ambient fiber quotient finiteness and SAME polynomial Jacobian remain to be
fully assembled into the conditional socle bridge. Original homogeneous
relation, simultaneous Bertini union, Section 4 geometric sheaf lifting,
global Proj comparison and actual projective intersection remain OPEN.

Accepted exact private source hashes and successful compiler/axiom logs:
checkpoint95-private-provenance.json. Public sources use Linear-prefixed
imports and omit temporary print commands; full public rebuild and audit
must pass before this checkpoint is counted or published.
