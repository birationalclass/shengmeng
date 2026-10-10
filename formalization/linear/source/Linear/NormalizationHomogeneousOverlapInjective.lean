module
public import Linear.NormalizationHomogeneousAffineDualOverlapLocalization
public import Linear.ProjectiveNativeGlobalChartDualityViaGeneric
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {K R : Type u} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
/-- Injectivity of the genuine base-overlap map is derived from the original
domain and nonzero coordinates; no overlap-injectivity certificate is assumed. -/
theorem homogeneousAwayOverlap_injective
    (e : ℕ) (a b : R) (hb : b ∈ 𝒜 e) (hab : a*b ≠ 0) :
    Function.Injective (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)) := by
  have ha : a ≠ 0 := (mul_ne_zero_iff.mp hab).1
  have h1 := IsLocalization.injective (Localization.Away a)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have h2 := IsLocalization.injective (Localization.Away (a*b))
    (powers_le_nonZeroDivisors_of_noZeroDivisors hab)
  let hu : IsUnit (algebraMap R (Localization.Away (a*b)) a) :=
    isUnit_of_dvd_unit (map_dvd _ (show a ∣ a*b from ⟨b,rfl⟩))
      (IsLocalization.Away.algebraMap_isUnit (a*b))
  let f := Localization.awayLift (algebraMap R (Localization.Away (a*b))) a hu
  have hf : Function.Injective f :=
    (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers a) f).mpr (by
      intro x y
      simp only [f,Localization.awayLift,IsLocalization.Away.lift_eq,h1.eq_iff,h2.eq_iff])
  intro x y h
  apply HomogeneousLocalization.val_injective
  apply hf
  simpa only [HomogeneousLocalization.val_awayMap] using congrArg HomogeneousLocalization.val h
/-- The actual original linear normalization base has injective overlap
maps for EVERY pair of original coordinates, including i=j. -/
theorem projectiveCoordinateHomogeneousOverlap_injective
    (r : ℕ) (i j : Fin (r+1)) :
    Function.Injective (HomogeneousLocalization.awayMap
      (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
      (MvPolynomial.isHomogeneous_X ℂ j)
      (rfl : MvPolynomial.X i * MvPolynomial.X j = MvPolynomial.X i * MvPolynomial.X j)) := by
  exact homogeneousAwayOverlap_injective
    (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ) 1
    (MvPolynomial.X i) (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j)
    (mul_ne_zero (MvPolynomial.X_ne_zero i) (MvPolynomial.X_ne_zero j))
end LinearStudy
