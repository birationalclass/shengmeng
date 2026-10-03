module
public import Negativity.ActualRelativeCechForgetKernel
public import Negativity.GradedModuleComponentVanishing
public import Negativity.RelativeCechSectionLifting

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- If an actual kernel class is an ambient coboundary, multiplication by an
actual coefficient of I^m makes its primitive lie in every smaller I^t.
Thus the corresponding transition class is zero. -/
theorem actual_relative_cech_kernel_scalar_transition_zero
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) (m d t : ℕ) (htm : t ≤ m)
    (r : Γ(Y, ⊤)) (hr : r ∈ (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ m)
    (a : actualClosedCechHOne ((I ^ d).comap f).subschemeι (fun j => (U j).1))
    (ha : actualClosedCechForget ((I ^ d).comap f).subschemeι
      (fun j => (U j).1) a = 0)
    (j : ((I ^ t).comap f).subscheme ⟶ ((I ^ (m + d)).comap f).subscheme)
    (hj : j ≫ ((I ^ (m + d)).comap f).subschemeι = ((I ^ t).comap f).subschemeι) :
    actualClosedCechHOneTransition j ((I ^ (m + d)).comap f).subschemeι
      (fun j => (U j).1) (actualRelativeCechGradedHOne f I U hU m d r hr a) = 0 := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective a
  change ((actualClosedCechForgetCycle ((I ^ d).comap f).subschemeι
    (fun j => (U j).1) z) : actualCechHOne X (fun j => (U j).1)) = 0 at ha
  obtain ⟨b, hb⟩ := (QuotientAddGroup.eq_zero_iff _).mp ha
  have hdb : actualCechDifference X (fun j => (U j).1) b = z.1 :=
    congrArg Subtype.val hb
  let v : (actualCechPullbackZero
      (j ≫ ((I ^ (m + d)).comap f).subschemeι) (fun j => (U j).1)).ker :=
    ⟨actualCechScaleZero X (fun j => (U j).1) (f.appTop r) b, by
      funext k
      change (j ≫ ((I ^ (m + d)).comap f).subschemeι).app (U k).1
        (actualSectionRestriction X le_top (f.appTop r) * b k) = 0
      rw [hj]
      have hr' : r ∈ (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ t :=
        Ideal.pow_le_pow_right htm hr
      have hs := actual_base_ideal_local_pullback_mem f (I ^ t) r hr' (U k)
      have hp := Ideal.mul_mem_right (b k) _ hs
      rw [← IdealSheafData.ker_subschemeι_app] at hp
      exact hp⟩
  change ((actualClosedCechCycleTransition j ((I ^ (m + d)).comap f).subschemeι
    (fun j => (U j).1) (actualRelativeCechGradedCycle f I U hU m d r hr z)) :
      actualClosedCechHOne (j ≫ ((I ^ (m + d)).comap f).subschemeι)
        (fun j => (U j).1)) = 0
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨v, ?_⟩
  apply Subtype.ext
  change actualCechDifference X (fun j => (U j).1)
    (actualCechScaleZero X (fun j => (U j).1) (f.appTop r) b) =
      actualCechScaleOne X (fun j => (U j).1) (f.appTop r) z.1
  rw [actual_cech_difference_scale, hdb]

#print axioms actual_relative_cech_kernel_scalar_transition_zero
end
end Negativity
