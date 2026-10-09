# Actual closed zero-scheme pullback and reduced native linear sections

Library-first discovery inspected these official mathlib pages and pinned code:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Pullbacks.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient/Operations.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Properties.html

Pinned mathlib: 2a885768dae569d938bb9ff3474da6a8753bb90a.
Reuse isPullback_SpecMap_of_isPushout, IsPullback.of_iso,
IsClosedImmersion.spec_of_surjective, Ideal.quotientMap, quotientEquiv,
DoubleQuot.quotQuotEquivQuotSup, Ideal.map_span, Set.range_comp',
Ideal.isRadical_iff_quotient_reduced, isReduced_of_injective and
Module.Finite.of_injective. Read full pinned types before adapting them.

The existing original-f map has an exact ideal-image formula but does not
alone construct its CLOSED zero-scheme fiber product. No applicable ready
CommRingCat quotient-pushout theorem was found in the focused search. Prove
that pushout by the actual quotient universal property, apply mathlib's
contravariant Spec theorem, then transport through the actual native chart
and denominator-open scheme isomorphisms. Both closed immersions are actual
quotient morphisms. The source equations are the SAME original-f substitution.

Generic radical cone fibers of the original linear normalization do not alone
prove the target projective linear-section quotient is reduced. Derive the
needed denominator units from the original finite linear normalization and
homogeneous equation evaluation. Construct an explicit INJECTIVE homomorphism
from the original affine linear-section quotient into the actual cone fiber,
with an explicit left inverse, retaining all nilpotents. Derive its reducedness
and finite dimension. Use original homogeneous avoidance to choose a nonempty
target open satisfying every required denominator condition. Finally construct
the actual native closed quotient ring equivalence with this affine section;
transfer reducedness to the original native chart closed scheme.

Scope: complex original integral V and original finite linear normalization;
for pullbacks use original positive-degree surjective f with total invariance.
Every scheme claim here is on the first native coordinate chart and its actual
denominator open. Reducedness of the SOURCE pulled common-zero scheme,
global Proj coverage/all-chart gluing, geometric Koszul, canonical embedding,
duality/Serre uniform Q lifting and actual intersection remain unproved.
This is not completion of current Lemma 4.1, Lemma 4.2 or Linearity Theorem.

Private compilation and standard-axiom records are enumerated in
checkpoint116-private-provenance.json. Public modules omit diagnostic prints
and require their own full project build and declaration audit before freezing.
