module

public import Negativity.RelativeIntegralClosureFinite
public import Negativity.CurveFunctionField
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem generic_stalk_preimage_nonempty_open (Y : Scheme.{u}) [IsIntegral Y]
    (U : Y.Opens) [Nonempty U] :
    (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U = ⊤ := by
  ext z
  change (Y.fromSpecStalk (genericPoint Y)) z ∈ U ↔ True
  apply iff_true_intro
  have hz : z = IsLocalRing.closedPoint Y.functionField := by
    apply PrimeSpectrum.ext
    simp only [Ideal.eq_bot_of_prime]
  rw [hz, Scheme.fromSpecStalk_closedPoint]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using ‹Nonempty U›)

/-- The actual section ring above a nonempty target open embeds into
the target function field, compatibly with the actual generic-stalk map. -/
theorem generic_stalk_affine_functionField_embedding (Y : Scheme.{u}) [IsIntegral Y]
    (U : Y.Opens) [Nonempty U] :
    letI : Algebra Γ(Y, U) Γ(Spec Y.functionField,
      (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) :=
        ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
    ∃ j : Γ(Spec Y.functionField, (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)
      →ₐ[Γ(Y, U)] Y.functionField, Function.Bijective j := by
  let f := Y.fromSpecStalk (genericPoint Y)
  let : Algebra Γ(Y, U) Γ(Spec Y.functionField, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let r : Γ(Spec Y.functionField, ⊤) ⟶ Γ(Spec Y.functionField, f ⁻¹ᵁ U) :=
    (Spec Y.functionField).presheaf.map (homOfLE le_top).op
  have hr : IsIso r := by
    have hp := generic_stalk_preimage_nonempty_open Y U
    have : IsIso (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)) := by
      exact homOfLE_isIso_of_eq _ hp
    infer_instance
  let e : Γ(Spec Y.functionField, f ⁻¹ᵁ U) ⟶ Y.functionField :=
    inv r ≫ (Scheme.ΓSpecIso Y.functionField).hom
  have he : IsIso e := by dsimp [e]; infer_instance
  have hcomp : f.app U ≫ e = Y.germToFunctionField U := by
    have hη : genericPoint Y ∈ U :=
      ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
        (by simpa using ‹Nonempty U›)
    rw [Scheme.fromSpecStalk_app hη]
    dsimp [e, r]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  let j : Γ(Spec Y.functionField, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Y.functionField := {
    __ := e.hom
    commutes' a := congrArg (fun h : Γ(Y, U) ⟶ Y.functionField => h a) hcomp }
  exact ⟨j, ConcreteCategory.bijective_of_isIso e⟩

/-- Final theorem: the actual relative normalization of an integral
finite-type scheme in its generic field is a finite Scheme morphism.
This proves the standard normalization finiteness for varieties over
perfect (hence algebraically closed) fields in arbitrary characteristic. -/
theorem finiteType_perfectField_normalization_isFinite
    (Y : Scheme.{u}) [IsIntegral Y] (k : Type u) [Field k] [PerfectField k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b] :
    IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  let f := Y.fromSpecStalk (genericPoint Y)
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · have : Nonempty U := hne
    let A := Γ(Y, U)
    let c : k →+* A := (Spec.preimage (hU.fromSpec ≫ b)).hom
    let : Algebra k A := c.toAlgebra
    have hc : c.FiniteType := by
      apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
      rw [Spec.map_preimage]
      infer_instance
    have : Algebra.FiniteType k A := hc
    have : IsFractionRing A Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y U hU
    let : Algebra A Γ(Spec Y.functionField, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    obtain ⟨j, hj⟩ := generic_stalk_affine_functionField_embedding Y U
    have : Module.Finite A (integralClosure A Γ(Spec Y.functionField, f ⁻¹ᵁ U)) :=
      finiteType_perfectField_relative_integralClosure_finite
        k A Y.functionField Y.functionField _ j hj.injective
    rw [Scheme.Hom.fromNormalization_app f hU, CommRingCat.hom_comp]
    exact (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).surjective).comp
        (RingHom.finite_algebraMap.mpr inferInstance)
  · have hbot : U = ⊥ := by
      apply bot_unique
      intro y hy
      exact (hne ⟨⟨y, hy⟩⟩).elim
    have : IsEmpty U := not_nonempty_iff.mp hne
    have : IsEmpty (f.fromNormalization ⁻¹ᵁ U) :=
      ⟨fun x => (hne ⟨⟨f.fromNormalization x.1, x.2⟩⟩).elim⟩
    have : IsIso (f.fromNormalization ∣_ U) := inferInstance
    have : IsIso (f.fromNormalization.app U) :=
      (isIso_morphismRestrict_iff_isIso_app f.fromNormalization hU).mp inferInstance
    exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (f.fromNormalization.app U)).surjective

end
end Negativity
