# Actual generic scalar fibers of the original linear normalization

Official mathlib documentation searched first:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/TensorProduct/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/TensorProduct/Quotient.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Nullstellensatz.html

Pinned mathlib commit: 2a885768dae569d938bb9ff3474da6a8753bb90a.
Reused includeRight_surjective, includeLeftRingHom_comp_algebraMap, the existing
audited generic module-rank open, unramified evaluation quotient, and finite
reduced scalar-point cardinality. Polynomial funext proves the target open
away from the zero-th target coordinate has a scalar point over the infinite field.

The actual base change K tensor_R A is proved finite and reduced on the
constructed open. Its dimension and scalar-point cardinality equal the
same original map's generic module rank. No fiber dimension, reducedness,
point count or projection tuple is assumed. The original V wrapper constructs
the same degree-one tuple, finite injection, actual dimension and no basepoint.

Still open: comparison of these tensor-product points with the actual
projective linear section; generic rank equals degree V; simultaneous Bertini;
Section 4 fixed-degree geometric lifting and actual intersection. Full theorem UNPROVED.
