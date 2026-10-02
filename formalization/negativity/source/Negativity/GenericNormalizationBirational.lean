module

public import Negativity.GenericNormalizationNormal
public import Negativity.CodimensionOne
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: the actual normalization map of an integral finite-type
perfect-field scheme is birational in the geometric sense: it is an
isomorphism above a nonempty open of the original scheme. The generic
section is spread out using proved finiteness, then its dominant image
and separatedness establish the actual inverse. -/
theorem finiteType_perfectField_normalization_birational
    (Y : Scheme.{u}) [IsIntegral Y] (k : Type u) [Field k] [PerfectField k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b] :
    BirationalMorphism (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  let g := Y.fromSpecStalk (genericPoint Y)
  let f := g.fromNormalization
  have : IsFinite f := finiteType_perfectField_normalization_isFinite Y k b
  obtain ⟨U, hη, s, hspread, hs⟩ :=
    spread_out_of_isGermInjective' (𝟙 Y) f g.toNormalization
      (by simp [g, f])
  have hsf : s ≫ f = U.ι := by simpa using hs
  have hUs : Set.range s ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change f (s x) ∈ U
    rw [← Scheme.Hom.comp_apply, hsf]
    exact x.2
  let s' : U.toScheme ⟶ (f ⁻¹ᵁ U) := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι s hUs
  have hs'ι : s' ≫ (f ⁻¹ᵁ U).ι = s := IsOpenImmersion.lift_fac _ _ hUs
  have : IsDominant s := by
    have : IsDominant (U.fromSpecStalkOfMem (genericPoint Y) hη ≫ s) := by
      rw [← hspread]
      infer_instance
    exact IsDominant.of_comp (U.fromSpecStalkOfMem (genericPoint Y) hη) s
  have : IsDominant s' := by
    have : IsDominant (s' ≫ (f ⁻¹ᵁ U).ι) := by rw [hs'ι]; infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion s' (f ⁻¹ᵁ U).ι
  have : Nonempty (f ⁻¹ᵁ U) := ⟨s' ⟨genericPoint Y, hη⟩⟩
  refine ⟨U, ⟨⟨genericPoint Y, hη⟩⟩, ?_⟩
  apply separated_dominant_section_isIso (f ∣_ U) s'
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, hs'ι, hsf, Category.id_comp]

end
end Negativity
