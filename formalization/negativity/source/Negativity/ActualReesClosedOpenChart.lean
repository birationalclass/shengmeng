module
public import Negativity.ActualReesOpenChart
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open TopologicalSpace Polynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

def actualReesClosedOpenChart (f : X ⟶ Spec (.of R)) (I : Ideal R) (U : X.Opens) :
    actualRelativeReesScheme (U.ι ≫ f) I ⟶ actualRelativeReesScheme f I :=
  IdealSheafData.subschemeMap (actualPolynomialReesMap (U.ι ≫ f) I).ker
    (actualPolynomialReesMap f I).ker (actualBaseChangeOpenChart f (actualReesProjection I) U)
    (IdealSheafData.le_map_iff_comap_le.mpr (actual_rees_open_chart_kernel f I U).le)

@[reassoc (attr := simp)]
theorem actual_rees_closed_open_chart_fac (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (U : X.Opens) :
    actualReesClosedOpenChart f I U ≫ (actualPolynomialReesMap f I).ker.subschemeι =
      (actualPolynomialReesMap (U.ι ≫ f) I).ker.subschemeι ≫
        actualBaseChangeOpenChart f (actualReesProjection I) U := by
  exact IdealSheafData.subschemeMap_subschemeι _ _ _ _

theorem actual_rees_closed_open_chart_isPullback (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (U : X.Opens) :
    IsPullback (actualPolynomialReesMap (U.ι ≫ f) I).ker.subschemeι
      (actualReesClosedOpenChart f I U)
      (actualBaseChangeOpenChart f (actualReesProjection I) U)
      (actualPolynomialReesMap f I).ker.subschemeι := by
  apply isPullback_of_isClosedImmersion
  · exact (actual_rees_closed_open_chart_fac f I U).symm
  · simpa only [IdealSheafData.ker_subschemeι] using actual_rees_open_chart_kernel f I U

instance actualReesClosedOpenChart_isOpenImmersion (f : X ⟶ Spec (.of R))
    (I : Ideal R) (U : X.Opens) : IsOpenImmersion (actualReesClosedOpenChart f I U) :=
  MorphismProperty.of_isPullback (actual_rees_closed_open_chart_isPullback f I U) inferInstance

abbrev actualRelativeReesToSource (f : X ⟶ Spec (.of R)) (I : Ideal R) :
    actualRelativeReesScheme f I ⟶ X :=
  (actualPolynomialReesMap f I).ker.subschemeι ≫ pullback.fst f (actualReesProjection I)

instance actualRelativeReesToSource_isAffineHom (f : X ⟶ Spec (.of R)) (I : Ideal R) :
    IsAffineHom (actualRelativeReesToSource f I) := by
  have : IsAffineHom (pullback.fst f (actualReesProjection I)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  dsimp [actualRelativeReesToSource]
  infer_instance

/-- Final theorem: the actual Rees closed image over an open U embeds
as exactly the inverse-image open of U in the global Rees closed image.
This realizes the actual chart cover and its geometric restriction maps. -/
theorem actual_rees_closed_open_chart_range (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (U : X.Opens) :
    (actualReesClosedOpenChart f I U).opensRange = actualRelativeReesToSource f I ⁻¹ᵁ U := by
  let h := actual_rees_closed_open_chart_isPullback f I U
  have he := congrArg (fun j : actualRelativeReesScheme (U.ι ≫ f) I ⟶
      actualRelativeReesScheme f I => Set.range j) h.isoPullback_hom_snd
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at he
  have hs : Function.Surjective h.isoPullback.hom := by
    intro x
    obtain ⟨z, hz⟩ := h.isoPullback.hom.homeomorph.surjective x
    exact ⟨z, (Scheme.Hom.homeomorph_apply h.isoPullback.hom z).symm.trans hz⟩
  rw [Set.range_eq_univ.mpr hs,
    Set.image_univ] at he
  apply Opens.ext
  change Set.range (actualReesClosedOpenChart f I U) =
    (actualRelativeReesToSource f I ⁻¹ᵁ U : Set (actualRelativeReesScheme f I))
  rw [← he, IsOpenImmersion.range_pullbackSnd, actual_base_change_open_chart_range]
  rfl

end
end Negativity
