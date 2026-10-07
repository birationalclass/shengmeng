# Milestone 8: relative pairing constructed from actual finite flat equations

The full Linearity Theorem and the general derivative-Jacobian comparison
remain unproved. This milestone contains 196 project proofs, 54 definitions
and 340 audited declarations including separately counted ports.

FiniteSpecialization.lean constructs the actual quotient specialization as
a surjective semilinear map. Original relative finiteness implies finite
dimension of K[[z]]/(specialized equations), hence Artinianity. Original
regularity and flatness imply closed-fiber regularity; together these give
the constructed closed-fiber perfect pairing and coefficient-determinant
trace formula, without extra closed-fiber hypotheses.

TensorSpecialization.lean identifies the actual residue-field tensor
product with this equation quotient. It proves the 1 tensor quotient-class
formula and the residue-field scalar formula. SocleTransport.lean transfers
the proved scalar socle through the actual ring and residue-field
isomorphisms. Combining with the existing functional/Gram determinant lift
constructs the B-valued relative perfect multiplication pairing of A.

The final pairing theorem assumes only original regular equations and
finite flatness over B=K[[s]]. It does not assume a socle theorem, finite
closed fiber, or perfect pairing. It holds over any field and for positive
equation/parameter counts as specified in its exact Lean type.

This does not identify the actual derivative Jacobian with a trace element.
That identity, its survival for arbitrary parameter lifts and the remaining
global projective-geometric proof are still unfinished. Do not count this
relative-pairing milestone as completion of manuscript Lemma 2.1.

Library-first discovery inspected official documentation and pinned
Module.Finite.of_surjective, quotient/tensor equivalences, residue-field
and tensor-scalar APIs. All declared proofs were compiled and axioms audited:
no sorryAx or project axiom. Deployment evidence is recorded separately.
