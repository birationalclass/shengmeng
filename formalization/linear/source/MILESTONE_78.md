# Local checkpoint 78: actual function-field degree of whole fibers

The exact `LinearityTheoremGoal` remains **unproved**.

The original denominator chart A=B_a is proved to have the original
Frac(B) as its fraction field under awayFractionEmbedding. The original
pullback B -> A has generic rank equal to [Frac(B):gamma.fieldRange],
where gamma is the actual original function-field pullback.

Although source and target use the same underlying domain, their scalar
actions are distinct. The actual intermediate-field range separates
these roles. Its target fraction-ring model and the source fraction-ring
model give two explicit scalar towers, verified by the previously proved
original pullback commuting square. mathlib IsFractionRing.finrank_eq
then applies to the original map, without supplying a degree value.

Combined with checkpoint 77, this constructs a nonempty ORIGINAL target
open on which EVERY WHOLE original projective point fiber has cardinality
equal to this actual function-field extension degree.

The public build and full kernel audit pass: 997 project theorem proofs,
192 definitions, 1385 audited declarations and 303 source files. Only
propext, Classical.choice and Quot.sound occur; no sorryAx or custom axiom.

This degree is NOT yet computed as q^r. Scheme gluing, geometric
dimension, Bertini sections, uniform global duality/Serre lifting and
geometric Bezout remain separate obligations. The full theorem is not
yet proved.
