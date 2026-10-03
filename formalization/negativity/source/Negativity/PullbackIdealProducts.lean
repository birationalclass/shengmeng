module

public import Negativity.AffinePullbackIdeal
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actual_affine_ideal_pullback_mul {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I J : Y.IdealSheafData) :
    (I * J).comap f = I.comap f * J.comap f := by
  apply IdealSheafData.ext_of_isAffine
  rw [actual_affine_ideal_pullback, IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul,
    IdealSheafData.ideal_mul, Pi.mul_apply, actual_affine_ideal_pullback,
    actual_affine_ideal_pullback]

theorem actual_open_ideal_pullback_mul {X : Scheme.{u}} (U : X.Opens)
    (I J : X.IdealSheafData) :
    (I * J).comap U.ι = I.comap U.ι * J.comap U.ι := by
  ext W : 2
  simp only [IdealSheafData.ideal_comap_of_isOpenImmersion, Opens.ι_appIso,
    Iso.refl_inv, IdealSheafData.ideal_mul, Pi.mul_apply]
  rfl

theorem actual_ideal_pullback_mul_over_affine_base {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) (I J : Y.IdealSheafData) :
    (I * J).comap f = I.comap f * J.comap f := by
  ext U : 2
  have : IsAffine U := U.2
  have hu : ((I * J).comap f).comap U.1.ι =
      (I.comap f * J.comap f).comap U.1.ι := by
    rw [actual_open_ideal_pullback_mul, ← IdealSheafData.comap_comp,
      ← IdealSheafData.comap_comp, ← IdealSheafData.comap_comp,
      actual_affine_ideal_pullback_mul]
  have hh := congrArg (fun K : U.1.toScheme.IdealSheafData =>
    K.ideal ⟨⊤, isAffineOpen_top U.1⟩) hu
  simp only [IdealSheafData.ideal_comap_of_isOpenImmersion, Opens.ι_appIso,
    Iso.refl_inv] at hh
  change ((I * J).comap f).ideal
      ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1).image_of_isOpenImmersion U.1.ι⟩ =
    (I.comap f * J.comap f).ideal
      ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1).image_of_isOpenImmersion U.1.ι⟩ at hh
  have heU : (⟨U.1.ι ''ᵁ ⊤,
      (isAffineOpen_top U.1).image_of_isOpenImmersion U.1.ι⟩ : X.affineOpens) = U :=
    Subtype.ext U.1.ι_image_top
  exact Eq.mp (congrArg (fun V : X.affineOpens =>
    ((I * J).comap f).ideal V = (I.comap f * J.comap f).ideal V) heU) hh

/-- Final theorem: actual ideal-power thickenings pull back as powers
of the actual pulled-back ideal over an affine base, with arbitrary
nonaffine source. Multiplication and affine-chart restriction are proved
from actual scheme ideal pullback. No power-compatibility input is used. -/
theorem actual_ideal_pullback_pow_over_affine_base {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) (I : Y.IdealSheafData) (n : ℕ) :
    (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => simp only [pow_zero, IdealSheafData.one_eq_top, IdealSheafData.comap_top]
  | succ n hn =>
    rw [pow_succ, actual_ideal_pullback_mul_over_affine_base, hn, pow_succ]

end
end Negativity
