module

public import Negativity.ActualRelativeReesScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
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

def actualBaseChangeOpenChart (f : X ⟶ Spec (.of R))
    {T : Scheme.{u}} (g : T ⟶ Spec (.of R)) (U : X.Opens) :
    pullback (U.ι ≫ f) g ⟶ pullback f g :=
  pullback.map _ _ _ _ U.ι (𝟙 T) (𝟙 (Spec (.of R))) (by simp) (by simp)

instance actualBaseChangeOpenChart_isOpenImmersion (f : X ⟶ Spec (.of R))
    {T : Scheme.{u}} (g : T ⟶ Spec (.of R)) (U : X.Opens) :
    IsOpenImmersion (actualBaseChangeOpenChart f g U) := by
  dsimp [actualBaseChangeOpenChart]
  infer_instance

theorem actual_base_change_open_chart_range (f : X ⟶ Spec (.of R))
    {T : Scheme.{u}} (g : T ⟶ Spec (.of R)) (U : X.Opens) :
    (actualBaseChangeOpenChart f g U).opensRange = pullback.fst f g ⁻¹ᵁ U := by
  apply Opens.ext
  simp [actualBaseChangeOpenChart, Scheme.Pullback.range_map]

theorem actual_rees_open_chart_square (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (U : X.Opens) :
    actualPolynomialReesMap (U.ι ≫ f) I ≫ actualBaseChangeOpenChart f (actualReesProjection I) U =
      actualBaseChangeOpenChart f actualPolynomialProjection U ≫ actualPolynomialReesMap f I := by
  apply pullback.hom_ext <;>
    simp [actualPolynomialReesMap, actualBaseChangeOpenChart, pullback.map]

theorem actual_rees_open_chart_isPullback (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (U : X.Opens) :
    IsPullback (actualPolynomialReesMap (U.ι ≫ f) I)
      (actualBaseChangeOpenChart f actualPolynomialProjection U)
      (actualBaseChangeOpenChart f (actualReesProjection I) U)
      (actualPolynomialReesMap f I) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (actual_rees_open_chart_square f I U).symm
  rw [actual_base_change_open_chart_range, actual_base_change_open_chart_range,
    ← Scheme.Hom.comp_preimage]
  congr 1
  simp [actualPolynomialReesMap, pullback.map]

/-- The genuine closed-image ideal restricts to the genuine closed-image
ideal on every actual open chart. There is no assumed image/base-change
compatibility, and no flatness condition. -/
theorem actual_rees_open_chart_kernel (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (U : X.Opens) :
    (actualPolynomialReesMap f I).ker.comap (actualBaseChangeOpenChart f (actualReesProjection I) U) =
      (actualPolynomialReesMap (U.ι ≫ f) I).ker := by
  have := actual_polynomial_rees_map_affine f I
  apply IdealSheafData.ext
  funext V
  rw [IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (ker_ideal_of_isPullback_of_isOpenImmersion
    (actualPolynomialReesMap f I) (actualPolynomialReesMap (U.ι ≫ f) I)
    (actualBaseChangeOpenChart f actualPolynomialProjection U)
    (actualBaseChangeOpenChart f (actualReesProjection I) U)
    (actual_rees_open_chart_isPullback f I U) V).symm

/-- Final comparison: the Rees closed image on an actual open chart
is the corresponding actual open subscheme of the global Rees closed
image. The ideal compatibility is proved above. -/
def actualReesOpenChartIso (f : X ⟶ Spec (.of R)) (I : Ideal R) (U : X.Opens) :
    actualRelativeReesScheme (U.ι ≫ f) I ≅
      ((actualPolynomialReesMap f I).ker.subschemeι ⁻¹ᵁ
        (actualBaseChangeOpenChart f (actualReesProjection I) U).opensRange).toScheme := by
  let j := actualBaseChangeOpenChart f (actualReesProjection I) U
  let K := (actualPolynomialReesMap f I).ker
  have h : (actualPolynomialReesMap (U.ι ≫ f) I).ker = K.comap j :=
    (actual_rees_open_chart_kernel f I U).symm
  exact eqToIso (congrArg IdealSheafData.subscheme h) ≪≫
    K.comapIso j ≪≫ pullbackSymmetry _ _ ≪≫
    asIso (pullback.map K.subschemeι j K.subschemeι j.opensRange.ι
      (𝟙 _) j.isoOpensRange.hom (𝟙 _) (by simp) (by simp)) ≪≫
    pullbackRestrictIsoRestrict K.subschemeι j.opensRange

end
end Negativity
