module

public import Negativity.NormalizedCurveIntersection
public import Negativity.FunctionFieldFunctoriality
public import Negativity.CurveIntersectionDegree
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: the Cartier degree formula for any complete integral
source curve and a complete normal target curve. Source normalization
is constructed and its function field is identified with the original
source function field. Arbitrary characteristic and inseparable degree
are included. -/
theorem complete_integral_curve_cartier_intersection_degree
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian X]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdC : Order.krullDim C = 1) (hdX : Order.krullDim X = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) [IsProper b]
    (f : C ⟶ X) [IsProper f] [IsDominant f]
    {ι : Type*} (A : CartierAtlas X ι) :
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace b
    letI : Algebra X.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
    normalizedCartierCurveIntersection hdC k (f ≫ b) f A =
      (Module.finrank X.functionField C.functionField : ℤ) * cartierTotalOrder X hnX A := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace b
  let : Algebra X.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
  let n := C.fromSpecStalk (genericPoint C)
  have h := complete_integral_curve_normalization_properties C hdC k (f ≫ b)
  have : IsFinite n.fromNormalization := h.1
  have : IsLocallyNoetherian n.normalization := h.2.2.2.2.2.1
  have : IsProper (n.fromNormalization ≫ f) := inferInstance
  have : IsDominant n.fromNormalization := birationalMorphism_dominant n.fromNormalization h.2.1
  let : Algebra C.functionField n.normalization.functionField :=
    (dominantFunctionFieldMap n.fromNormalization).toAlgebra
  let : Algebra X.functionField n.normalization.functionField :=
    (dominantFunctionFieldMap (n.fromNormalization ≫ f)).toAlgebra
  have : IsScalarTower X.functionField C.functionField n.normalization.functionField :=
    IsScalarTower.of_algebraMap_eq' (dominantFunctionFieldMap_comp n.fromNormalization f)
  have := birationalMorphism_generic_stalk_isIso n.fromNormalization h.2.1
  let φ : C.functionField ⟶ n.normalization.functionField :=
    (C.presheaf.stalkCongr (.of_eq (dominant_genericPoint_eq n.fromNormalization))).inv ≫
      n.fromNormalization.stalkMap (genericPoint n.normalization)
  have hφ : IsIso φ := by dsimp only [φ]; infer_instance
  let e : C.functionField ≃ₐ[C.functionField] n.normalization.functionField :=
    AlgEquiv.ofBijective (Algebra.ofId C.functionField n.normalization.functionField)
      (ConcreteCategory.bijective_of_isIso φ)
  have hdeg : Module.finrank X.functionField n.normalization.functionField =
      Module.finrank X.functionField C.functionField :=
    (e.restrictScalars X.functionField).toLinearEquiv.finrank_eq.symm
  have hI := complete_normal_curve_cartier_intersection_degree
    (generic_normalization_stalks_normal C) hnX h.2.2.2.2.1 hdX k b
    (n.fromNormalization ≫ f) A
  rw [hdeg] at hI
  exact hI

end
end Negativity
