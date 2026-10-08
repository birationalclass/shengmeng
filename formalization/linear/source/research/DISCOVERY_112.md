# Checkpoint 112 library discovery and equation-fiber scope

Online primary-source documentation was inspected:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/TensorProduct/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient/Nilpotent.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/TensorProduct/Tower.html

The full corresponding pinned local definitions and types were read:
`Ideal.Quotient.liftₐ`, `Ideal.Quotient.lift_mk`,
`Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap`,
`Algebra.TensorProduct.lift`, `includeLeft_surjective`,
`Algebra.TensorProduct.comm` and `Ideal.isRadical_iff_quotient_reduced`.
The original project supplies the already audited derived good-open theorem
`finite_injective_algHom_exists_reduced_rank_fibers` and
`polynomialZeroLocus_card_eq_finrank`.

The missing bridge is implemented by the actual quotient universal property.
It constructs a coefficient-field algebra equivalence

    (K[X]/I) tensor_(K[Y]) K = K[X]/(I+(L_i-w_i)).

The original polynomial substitution and scalar evaluation define the base
algebra actions. Their scalar towers and compatibility are proved explicitly.
The equivalence is not inferred from a point-set bijection. This allows
derived finiteness and reducedness of the actual tensor fiber to transfer
to the actual original equation quotient, hence its ideal is radical.

This is an affine polynomial-projection equation-ring bridge. It does NOT
yet compare the global projective Proj intersection, establish all pullback
scheme transversality, construct canonical sheaves/Koszul/proper duality,
produce uniform fixed-degree Q, or close the main theorem. Generic rank is
not redefined as projective degree. The original exact target remains open.
