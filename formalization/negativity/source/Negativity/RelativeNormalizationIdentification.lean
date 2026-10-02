module

public import Negativity.RelativeFieldNormalization
public import Negativity.GenericNormalizationBirational
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A dominant actual generic section of a finite morphism spreads to
an isomorphism on a nonempty target open. -/
theorem finite_dominant_generic_section_birational
    {N C : Scheme.{u}} [IsIntegral N] [IsIntegral C]
    (p : N ⟶ C) [IsFinite p]
    (s : Spec C.functionField ⟶ N) [IsDominant s]
    (hs : s ≫ p = C.fromSpecStalk (genericPoint C)) : BirationalMorphism p := by
  obtain ⟨U, hη, t, hspread, ht⟩ :=
    spread_out_of_isGermInjective' (𝟙 C) p s (by simpa using hs)
  have htp : t ≫ p = U.ι := by simpa using ht
  have hrange : Set.range t ⊆ Set.range (p ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change p (t x) ∈ U
    rw [← Scheme.Hom.comp_apply, htp]
    exact x.2
  let t' : U.toScheme ⟶ (p ⁻¹ᵁ U) := IsOpenImmersion.lift (p ⁻¹ᵁ U).ι t hrange
  have ht'ι : t' ≫ (p ⁻¹ᵁ U).ι = t := IsOpenImmersion.lift_fac _ _ hrange
  have : IsDominant t := by
    have : IsDominant (U.fromSpecStalkOfMem (genericPoint C) hη ≫ t) := by
      rw [← hspread]
      infer_instance
    exact IsDominant.of_comp (U.fromSpecStalkOfMem (genericPoint C) hη) t
  have : IsDominant t' := by
    have : IsDominant (t' ≫ (p ⁻¹ᵁ U).ι) := by rw [ht'ι]; infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion t' (p ⁻¹ᵁ U).ι
  have : Nonempty (p ⁻¹ᵁ U) := ⟨t' ⟨genericPoint C, hη⟩⟩
  refine ⟨U, ⟨⟨genericPoint C, hη⟩⟩, ?_⟩
  apply separated_dominant_section_isIso (p ∣_ U) t'
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, ht'ι, htp, Category.id_comp]

/-- Final theorem: an actual normal source of a finite dominant map is
the target's relative normalization in the actual source function field.
The comparison map is an actual Scheme isomorphism, proved via a dominant
generic section and normality. It is not supplied as an extra input. -/
theorem finiteType_perfectField_relative_normalization_source_isIso
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) [IsFinite f] [IsDominant f]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (k : Type u) [Field k] [PerfectField k]
    (b : X ⟶ Spec (.of k)) [LocallyOfFiniteType b] :
    IsIso (((C.fromSpecStalk (genericPoint C)) ≫ f).normalizationDesc
      (C.fromSpecStalk (genericPoint C)) f rfl) := by
  let g := C.fromSpecStalk (genericPoint C)
  let h := g ≫ f
  let p := h.normalizationDesc g f rfl
  have hp : p ≫ f = h.fromNormalization := h.normalizationDesc_comp g f rfl
  have : IsFinite h.fromNormalization :=
    finiteType_perfectField_relative_generic_normalization_isFinite f k b
  have : IsFinite (p ≫ f) := by rw [hp]; infer_instance
  have : IsFinite p := IsFinite.of_comp p f
  have hs : h.toNormalization ≫ p = g := h.toNormalization_normalizationDesc g f rfl
  exact finite_normal_birational_isIso p
    (finite_dominant_generic_section_birational p h.toNormalization hs) hnC

end
end Negativity
