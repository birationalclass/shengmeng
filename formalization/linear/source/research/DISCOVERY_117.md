# Finite reduced actual pullbacks of original linear sections

Library-first discovery used official mathlib documentation and inspected
the full types in pinned mathlib 2a885768dae569d938bb9ff3474da6a8753bb90a:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Maps.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient/Operations.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Properties.html

Reuse Ideal.prod_eq_iInf_of_pairwise_isCoprime, Ideal.mapHom and map_prod,
IsCoprime.map, Ideal.isRadical_iInf, Ideal.comap_injective_of_surjective,
MaximalSpectrum.isCoprime_of_ne, IsArtinianRing.nilradical_eq_iInf,
DoubleQuot.quotQuotEquivQuotSupₐ, Ideal.quotientKerAlgEquivOfSurjective,
Ideal.quotientEquivAlgOfEq and Module.Finite.of_injective. Exact first
isomorphisms preserve the original quotient ideals and their nilpotents.

A general nonflat ring map does not preserve arbitrary ideal intersections.
The target section is actually finite and reduced. Its actual maximal point
ideals are pairwise coprime, so their finite intersection is their product.
Extend that equality through the original map. Radicality follows from
radicality of the actual extended point ideals; finiteness follows by an
injective algebra map to the finite product of their actual fiber quotients.
No flatness or supplied source product decomposition is assumed.

The original fiber quotient universal property proves that extension of
the actual target point ideal is precisely the actual original-f fiber map
kernel. The original residue evaluations of the actual section quotient are
identified with actual normalized points of V. Their section equations are
proved to vanish, including projective representative scaling.

For the SAME original finite linear normalization, intersect the previously
constructed target radical-section open with the original homogeneous
avoidance open for the original-f general reduced whole fibers. Derive every
individual reduced fiber used above. This proves finite reduced pulled
equation quotients and reduced actual Spec schemes on a nonempty open.

Scope is the original first-coordinate chart and its original denominator
open. Source reducedness is not a hypothesis and the equation ideal is not
replaced by its radical. Global Proj coverage/gluing, geometric Koszul,
canonical embedding, duality/Serre uniform fixed-degree Q and actual
Cartier/Bézout intersection remain open. Main theorem UNPROVED.

Exact private source hashes and standard-axiom compilation records are in
checkpoint117-private-provenance.json. Public promotion requires a separate
full public build and declaration/source-range audit.
