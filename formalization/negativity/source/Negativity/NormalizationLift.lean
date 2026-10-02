module

public import Negativity.RelativeNormalizationIdentification
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem dominant_functionField_Spec_square
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) [IsDominant f] :
    Spec.map (CommRingCat.ofHom (dominantFunctionFieldMap f)) ≫
      X.fromSpecStalk (genericPoint X) = C.fromSpecStalk (genericPoint C) ≫ f := by
  change Spec.map ((X.presheaf.stalkCongr
    (.of_eq (dominant_genericPoint_eq f))).inv ≫ f.stalkMap (genericPoint C)) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, TopCat.Presheaf.stalkCongr_inv,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f

/-- Final theorem: an actual finite dominant map from a normal integral
scheme lifts to the actual normalization of its possibly nonnormal target.
The lift and its commuting square are constructed; the lift is finite and
dominant. No lift, local-order compatibility or projection identity is an input. -/
theorem exists_finite_dominant_normalization_lift
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) [IsFinite f] [IsDominant f]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (k : Type u) [Field k] [PerfectField k]
    (b : X ⟶ Spec (.of k)) [LocallyOfFiniteType b] :
    ∃ l : C ⟶ (X.fromSpecStalk (genericPoint X)).normalization,
      l ≫ (X.fromSpecStalk (genericPoint X)).fromNormalization = f ∧
      IsFinite l ∧ IsDominant l := by
  let g := C.fromSpecStalk (genericPoint C)
  let n := X.fromSpecStalk (genericPoint X)
  let h := g ≫ f
  let p := h.normalizationDesc g f rfl
  have : IsIso p := finiteType_perfectField_relative_normalization_source_isIso f hnC k b
  let v : Spec C.functionField ⟶ Spec X.functionField :=
    Spec.map (CommRingCat.ofHom (dominantFunctionFieldMap f))
  have : IsDominant v := by
    have hv : Function.Surjective v := by
      intro x
      refine ⟨IsLocalRing.closedPoint C.functionField, ?_⟩
      apply PrimeSpectrum.ext
      simp only [Ideal.eq_bot_of_prime]
    exact ⟨hv.denseRange⟩
  have H : h = (v ≫ n.toNormalization) ≫ n.fromNormalization := by
    rw [Category.assoc, n.toNormalization_fromNormalization]
    exact (dominant_functionField_Spec_square f).symm
  let d := h.normalizationDesc (v ≫ n.toNormalization) n.fromNormalization H
  have hd : d ≫ n.fromNormalization = h.fromNormalization :=
    h.normalizationDesc_comp _ _ H
  have hp : p ≫ f = h.fromNormalization := h.normalizationDesc_comp g f rfl
  let l := inv p ≫ d
  have hl : l ≫ n.fromNormalization = f := by
    dsimp only [l]
    rw [Category.assoc, hd, ← hp, IsIso.inv_hom_id_assoc]
  have : IsFinite l := by
    have : IsFinite (l ≫ n.fromNormalization) := by rw [hl]; infer_instance
    exact IsFinite.of_comp l n.fromNormalization
  have : IsDominant d := by
    have : IsDominant (h.toNormalization ≫ d) := by
      rw [h.toNormalization_normalizationDesc _ _ H]
      infer_instance
    exact IsDominant.of_comp h.toNormalization d
  exact ⟨l, hl, inferInstance, inferInstance⟩

end
end Negativity
