# Local checkpoint 77: whole fiber cardinality equals the original generic rank

The exact `LinearityTheoremGoal` remains **unproved**.

Starting from the ORIGINAL homogeneous f,V and chart pullback B -> A, a
nonzero element of the ORIGINAL target domain is constructed so that all
field-valued fibers over this open have dimension equal to finrank_B A.
The proof uses the constructed finite/free localization, compares its
actual residue tensor with the original tensor, and clears the free-locus
denominator. Neither freeness of the original module nor injectivity of a
rational-point evaluation is assumed.

Intersecting with the previously constructed reduced whole-fiber open
gives a nonempty original target open on which EVERY whole projective
point fiber has cardinality equal to this actual generic rank. The entire
fiber lies in the chosen source chart. The finite/reduced tensor and its
point bijection are derived from f,V, not supplied as inputs.

The public build and full kernel audit pass: 993 project theorem proofs,
192 definitions, 1381 audited declarations and 301 source files. Only
propext, Classical.choice and Quot.sound occur; no sorryAx or custom axiom.

The generic rank is not yet identified with q^r. Its comparison with the
actual function-field extension is the next bridge. Scheme gluing,
geometric dimension, Bertini sections, uniform global duality/Serre lifting
and geometric Bezout remain separate obligations. This is not a proof of
the full theorem.
