module

public import Negativity.FiniteFunctionField
public import Negativity.FiniteNormalizationGeometry
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: normalize the target of an actual finite dominant map
in the actual source function field. This relative normalization is finite,
including purely inseparable field extensions and nonnormal targets. -/
theorem finiteType_perfectField_relative_generic_normalization_isFinite
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) [IsFinite f] [IsDominant f]
    (k : Type u) [Field k] [PerfectField k]
    (b : X ⟶ Spec (.of k)) [LocallyOfFiniteType b] :
    IsFinite ((C.fromSpecStalk (genericPoint C)) ≫ f).fromNormalization := by
  let g := C.fromSpecStalk (genericPoint C)
  let h := g ≫ f
  let : Algebra X.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
  have : FiniteDimensional X.functionField C.functionField := finite_dominant_functionField_finite f
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · have : Nonempty U := hne
    have hη : f (genericPoint C) ∈ U := by
      rw [dominant_genericPoint_eq f]
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
    have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨genericPoint C, hη⟩⟩
    let A := Γ(X, U)
    let B := Γ(C, f ⁻¹ᵁ U)
    let S := Γ(Spec C.functionField, h ⁻¹ᵁ U)
    let : Algebra A B := (f.app U).hom.toAlgebra
    let : Algebra A S := (h.app U).hom.toAlgebra
    let : Algebra A C.functionField :=
      ((C.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom).toAlgebra
    have : IsScalarTower A B C.functionField := IsScalarTower.of_algebraMap_eq' rfl
    have := finite_curve_chart_generic_tower f U
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    let : Algebra B Γ(Spec C.functionField, g ⁻¹ᵁ f ⁻¹ᵁ U) :=
      (g.app (f ⁻¹ᵁ U)).hom.toAlgebra
    obtain ⟨j, hj⟩ := generic_stalk_affine_functionField_embedding C (f ⁻¹ᵁ U)
    let r : S ⟶ Γ(Spec C.functionField, g ⁻¹ᵁ f ⁻¹ᵁ U) :=
      (Spec C.functionField).presheaf.map
        (eqToHom (by simp [h])).op
    have hr : IsIso r := by dsimp only [r]; infer_instance
    have hcomp : h.app U ≫ r = f.app U ≫ g.app (f ⁻¹ᵁ U) := by
      dsimp only [h, r]
      rw [Scheme.Hom.comp_app]
      simp
    let jA : S →ₐ[A] C.functionField := {
      __ := j.toRingHom.comp r.hom
      commutes' a := by
        change j ((h.app U ≫ r) a) = _
        rw [hcomp]
        exact j.commutes (f.app U a) }
    let c : k →+* A := (Spec.preimage (hU.fromSpec ≫ b)).hom
    let : Algebra k A := c.toAlgebra
    have hc : c.FiniteType := by
      apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
      rw [Spec.map_preimage]
      infer_instance
    have : Algebra.FiniteType k A := hc
    have : Module.Finite A (integralClosure A S) :=
      finiteType_perfectField_relative_integralClosure_finite
        k A X.functionField C.functionField S jA
          (hj.injective.comp (ConcreteCategory.bijective_of_isIso r).injective)
    rw [Scheme.Hom.fromNormalization_app h hU, CommRingCat.hom_comp]
    exact (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (h.normalizationObjIso hU).inv).surjective).comp
        (RingHom.finite_algebraMap.mpr inferInstance)
  · have : IsEmpty U := not_nonempty_iff.mp hne
    have : IsEmpty (h.fromNormalization ⁻¹ᵁ U) :=
      ⟨fun x => (hne ⟨⟨h.fromNormalization x.1, x.2⟩⟩).elim⟩
    have : IsIso (h.fromNormalization ∣_ U) := inferInstance
    have : IsIso (h.fromNormalization.app U) :=
      (isIso_morphismRestrict_iff_isIso_app h.fromNormalization hU).mp inferInstance
    exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (h.fromNormalization.app U)).surjective

end
end Negativity
