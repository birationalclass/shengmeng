# Milestone 24: affine low-degree perfect pairing and Jacobian trace

The full Linearity Theorem remains **UNPROVED**. The manuscript is unchanged.

`affine_polynomial_low_degree_trace_pairing` constructs one actual perfect multiplication pairing on the affine polynomial quotient whose functional vanishes on every polynomial of degree below `sum(deg(P_i)-1)` and satisfies the actual derivative Jacobian trace formula. The field is algebraically closed of characteristic zero. Positive polynomial degrees, regular highest homogeneous parts and their origin-only common zero locus are explicit assumptions.

The construction descends the highest-component functional through the proved filtered ideal comparison. The universal difference determinant has bounded degree. Its contraction is proved scalar by expansion into left/right monomials. The scalar is nonzero by the actual highest-part coefficient determinant socle theorem. Scaling normalizes the contraction, which then constructs the perfect pairing and identifies its diagonal with the same universal determinant. Its multiplication image is the derivative Jacobian, giving the trace formula. No perfect pairing or vanishing functional is assumed in the final theorem.

Four modules: `PolynomialContraction`, `TopDeterminant`, `ContractionPairing`, `AffineDiagonal`. These results close the algebraic compatibility left open at milestones 20–23; they do not discharge the geometric hypothesis comparisons or the projective fiber relation.

Next: decompose a global perfect functional into point contributions and connect the relative socle element to the projective homogeneous relation. Actual highest-part regularity in the geometric setting, residue/chart compatibility, uniform Serre/proper-duality lifting and the geometric intersection bound remain open.

Library-first research reused the pinned mathlib tensor-polynomial API and actual Kaehler ideal (`Mathlib/RingTheory/TensorProduct/MvPolynomial`, `Mathlib/RingTheory/Kaehler/Basic`). Focused online and pinned-source discovery did not supply this complete filtered affine construction. Build, complete-type inspection and axiom audit are recorded separately from publication.
