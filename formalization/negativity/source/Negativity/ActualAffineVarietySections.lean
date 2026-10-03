module
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

@[instance_reducible]
def actualAffineVarietySectionAlgebra (k : Type u) [Field k]
    (Y : Scheme.{u}) [IsAffine Y] (b : Y ⟶ Spec (.of k)) :
    Algebra k Γ(Y, ⊤) :=
  (Spec.preimage (Y.isoSpec.inv ≫ b)).hom.toAlgebra

/-- Final theorem: every actual affine variety chart has a finite-type
algebra of functions over its actual base field. This constructs the
algebra required for the already verified relative kernel bound. -/
theorem actual_affine_variety_section_algebra_finite_type
    (k : Type u) [Field k] (Y : Scheme.{u}) [IsAffine Y]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b] :
    letI := actualAffineVarietySectionAlgebra k Y b
    Algebra.FiniteType k Γ(Y, ⊤) := by
  let := actualAffineVarietySectionAlgebra k Y b
  have hc : (Spec.preimage (Y.isoSpec.inv ≫ b)).hom.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [Spec.map_preimage]
    infer_instance
  exact hc

end
end Negativity
