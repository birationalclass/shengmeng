# Library discovery and precise correspondence for checkpoint 86

Checked against pinned mathlib 2a885768dae569d938bb9ff3474da6a8753bb90a.

Primary online discovery:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/RatFunc/Basic.html — `RatFunc.finrank_ratFunc_ratFunc`.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.html — actual image/adjoin maps and restriction of scalars.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html — `Algebra.finrank_eq_of_equiv_equiv`.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Algebraic/Basic.html — transcendence under powers and towers.

Pinned source inspected: RatFunc/Basic.lean, RatFunc/IntermediateField.lean,
IntermediateField/Basic.lean, IntermediateField/Adjoin/Defs.lean,
Algebraic/Basic.lean, Algebraic/Integral.lean, Dimension/Finrank.lean,
Dimension/Free.lean, Localization/FractionRing.lean and Algebra/Tower.lean.

The standard coefficient-extension degree theorem and compatible-isomorphism
degree theorem are reused. They do not themselves identify the whole actual
image field of the original cone endomorphism. The missing bridge was proved:

1. For an actual transcendental element s over E, adjoining the SAME s to
   a coefficient subfield R and to E preserves the degree [E:R]. The actual
   R(s)->E(s) map and commuting rational-function isomorphisms are constructed.
2. For F=E(t), the whole image of phi equals phi(E)(phi(t)). The coefficient
   image's extension degree is that of the actual restricted endomorphism.
3. The whole degree factors by the scalar tower. For the ORIGINAL f,V,
   phi(t)=u*t^q and the previously constructed rational-field isomorphism
   yield cone degree = q * projective ratio-field degree.
4. The actual cone degree q^deg(C), deg(C)=deg(P)+1 and q>0 give the actual
   projective degree q^deg(P). A constructed chart-field isomorphism transfers
   this degree to the actual chart pullback.
5. Previous whole-fiber and actual iterate results now calculate all general
   whole point fibers as (q^k)^deg(P), using ONE actual Hilbert polynomial P.

No geometric dimension or degree value, transcendence, perfect pairing,
field isomorphism or preselected good fiber is supplied as a conclusion input.
The geometric comparison deg(P)=dim(V), global residue/relation assembly,
canonical sheaf/Serre lifting and actual Cartier/Bezout inequality remain open.

Focused search for the next Hilbert/Krull-dimension bridge also inspected:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/NoetherNormalization.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/KrullDimension/Polynomial.html

No direct matching Hilbert-polynomial/Krull-dimension theorem was found in
these focused online and pinned-source searches. Noether normalization and
polynomial Krull dimension are reusable ingredients, not a completed bridge.
