module
public import Negativity.ActualSpecIdealPullback
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actual_affine_base_spec_ideal_pullback
    (Y : Scheme.{u}) [IsAffine Y] (J : Y.IdealSheafData) :
    (actualSpecIdealSheaf (J.ideal ⟨⊤, isAffineOpen_top Y⟩)).comap Y.toSpecΓ = J := by
  apply IdealSheafData.ext_of_isAffine
  rw [actual_affine_ideal_pullback, actual_spec_ideal_sheaf_top,
    Scheme.toSpecΓ_appTop, Ideal.map_map, ← CommRingCat.hom_comp]
  change Ideal.map
    ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv ≫ (Scheme.ΓSpecIso Γ(Y, ⊤)).hom).hom
    (J.ideal ⟨⊤, isAffineOpen_top Y⟩) = _
  rw [Iso.inv_hom_id]
  simp

theorem actual_affine_base_spec_power_pullback
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    (J : Y.IdealSheafData) (n : ℕ) :
    (((actualSpecIdealSheaf (J.ideal ⟨⊤, isAffineOpen_top Y⟩)) ^ n).comap
      (f ≫ Y.toSpecΓ)) = (J ^ n).comap f := by
  rw [IdealSheafData.comap_comp, actual_ideal_pullback_pow_over_affine_base,
    actual_affine_base_spec_ideal_pullback]

theorem actual_affine_base_spec_coefficient
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) (U : X.Opens) :
    (Scheme.ΓSpecIso Γ(Y, ⊤)).inv ≫ (f ≫ Y.toSpecΓ).appLE ⊤ U le_top =
      f.appLE ⊤ U le_top := by
  rw [Scheme.Hom.comp_appLE, ← Scheme.Hom.appTop, Scheme.toSpecΓ_appTop,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  simp only [Scheme.Hom.preimage_top]

/-- Final theorem: reduction of an actual affine base to Spec of its
global sections preserves both the actual thickening ideals and the
actual coefficient action, so Rees coordinates require no new bridge input. -/
theorem actual_affine_base_rees_coordinates
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    (J : Y.IdealSheafData) (n : ℕ) (U : X.Opens) :
    (((actualSpecIdealSheaf (J.ideal ⟨⊤, isAffineOpen_top Y⟩)) ^ n).comap
      (f ≫ Y.toSpecΓ)) = (J ^ n).comap f ∧
    (Scheme.ΓSpecIso Γ(Y, ⊤)).inv ≫ (f ≫ Y.toSpecΓ).appLE ⊤ U le_top =
      f.appLE ⊤ U le_top :=
  ⟨actual_affine_base_spec_power_pullback f J n,
    actual_affine_base_spec_coefficient f U⟩

end
end Negativity
