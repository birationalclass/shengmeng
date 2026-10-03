module
public import Negativity.AffinePullbackIdeal
public import Negativity.PullbackIdealProducts
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actual_affine_open_ideal_pullback {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) (I : Y.IdealSheafData) (U : X.affineOpens) :
    (I.comap f).ideal U =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map (f.appLE ⊤ U.1 le_top).hom := by
  let : IsAffine U.1.toScheme := U.2
  have h := actual_affine_ideal_pullback (U.1.ι ≫ f) I
  rw [IdealSheafData.comap_comp,
    IdealSheafData.ideal_comap_of_isOpenImmersion] at h
  simp only [Opens.ι_appIso, Iso.refl_inv] at h
  have heU : (⟨U.1.ι ''ᵁ ⊤,
      (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩ : X.affineOpens) = U :=
    Subtype.ext U.1.ι_image_top
  have hmap : (U.1.ι ≫ f).appTop =
      f.appLE ⊤ (U.1.ι ''ᵁ ⊤) le_top := by
    rw [Scheme.Hom.comp_appTop, Opens.ι_appTop]
    rfl
  have hh : (I.comap f).ideal
      ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map
        (f.appLE ⊤ (U.1.ι ''ᵁ ⊤) le_top).hom := by
    change Ideal.comap (RingHom.id Γ(X, U.1.ι ''ᵁ ⊤))
      ((I.comap f).ideal ⟨U.1.ι ''ᵁ ⊤,
        (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩) =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map (U.1.ι ≫ f).appTop.hom at h
    rw [Ideal.comap_id, hmap] at h
    exact h
  exact Eq.mp (congrArg (fun V : X.affineOpens => (I.comap f).ideal V =
    (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map (f.appLE ⊤ V.1 le_top).hom) heU) hh

/-- Final theorem: on every actual affine open, an ideal-power
thickening is precisely the extended power of the actual base ideal,
through the actual map on sections. -/
theorem actual_affine_open_ideal_power_pullback {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) (I : Y.IdealSheafData) (U : X.affineOpens) (n : ℕ) :
    ((I ^ n).comap f).ideal U =
      ((I.ideal ⟨⊤, isAffineOpen_top Y⟩).map (f.appLE ⊤ U.1 le_top).hom) ^ n := by
  rw [actual_affine_open_ideal_pullback, IdealSheafData.ideal_pow, Pi.pow_apply,
    Ideal.map_pow]

end
end Negativity
