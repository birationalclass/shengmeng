module

public import Negativity.ActualCechModule
public import Negativity.PullbackIdealProducts
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actual_base_ideal_local_pullback_mem {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    (r : Γ(Y, ⊤)) (hr : r ∈ I.ideal ⟨⊤, isAffineOpen_top Y⟩)
    (U : X.affineOpens) :
    actualSectionRestriction X le_top (f.appTop r) ∈ (I.comap f).ideal U := by
  have hp := I.le_map_comap f ⟨⊤, isAffineOpen_top Y⟩ hr
  rw [IdealSheafData.map, Scheme.Hom.ker_apply] at hp
  have hz : (I.comap f).subschemeι.appTop (f.appTop r) = 0 := hp
  rw [← IdealSheafData.ker_subschemeι_app]
  change (I.comap f).subschemeι.app U.1
    (actualSectionRestriction X le_top (f.appTop r)) = 0
  rw [← actual_section_restriction_naturality (I.comap f).subschemeι le_top]
  change actualSectionRestriction (I.comap f).subscheme _
    ((I.comap f).subschemeι.appTop (f.appTop r)) = 0
  rw [hz, map_zero]

/-- Final theorem: a coefficient in the actual m-th base ideal power
multiplies an actual n-th ideal Cech cocycle into the actual (m+n)-th
ideal cocycles. The scalar is the actual global pullback and actual local
ideal membership is proved. This is the genuine graded multiplication
needed for the Rees action; finite generation is not assumed or claimed. -/
theorem actual_relative_cech_graded_cocycle_multiplication
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ j k, IsAffineOpen (U j ⊓ U k))
    (m n : ℕ) (r : Γ(Y, ⊤))
    (hr : r ∈ (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ m)
    (a : actualClosedCechCocycles ((I ^ n).comap f).subschemeι U) :
    actualCechScaleOne X U (f.appTop r) a.1 ∈
      actualClosedCechCocycles ((I ^ (m + n)).comap f).subschemeι U := by
  constructor
  · funext j k
    change ((I ^ (m + n)).comap f).subschemeι.app (U j ⊓ U k)
      (actualSectionRestriction X le_top (f.appTop r) * a.1 j k) = 0
    let V : X.affineOpens := ⟨U j ⊓ U k, hU j k⟩
    have hs : actualSectionRestriction X le_top (f.appTop r) ∈
        ((I ^ m).comap f).ideal V :=
      actual_base_ideal_local_pullback_mem f (I ^ m) r hr V
    have ha : a.1 j k ∈ ((I ^ n).comap f).ideal V := by
      rw [← IdealSheafData.ker_subschemeι_app]
      exact congrArg (fun t : actualCechOne ((I ^ n).comap f).subscheme
        (fun j => ((I ^ n).comap f).subschemeι ⁻¹ᵁ U j) => t j k) a.2.1
    have hm : ((I ^ (m + n)).comap f).ideal V =
        ((I ^ m).comap f).ideal V * ((I ^ n).comap f).ideal V := by
      rw [pow_add, actual_ideal_pullback_mul_over_affine_base]
      rfl
    have hprod : actualSectionRestriction X le_top (f.appTop r) * a.1 j k ∈
        ((I ^ (m + n)).comap f).ideal V := by
      rw [hm]
      exact Ideal.mul_mem_mul hs ha
    rw [← IdealSheafData.ker_subschemeι_app] at hprod
    exact hprod
  · funext j k l
    rw [actual_cech_boundary_scale]
    have ha := congrArg (fun t : actualCechTwo X U => t j k l) a.2.2
    change actualCechBoundary X U a.1 j k l = 0 at ha
    rw [ha, mul_zero]
    rfl

end
end Negativity
