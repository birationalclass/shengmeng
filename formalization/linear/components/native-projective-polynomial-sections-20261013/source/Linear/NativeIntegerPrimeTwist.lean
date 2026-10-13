module
public import Linear.NativeProjectiveIntegerTwistChartFree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- The actual image of a nonvanishing homogeneous coordinate is a unit
in the original prime localization. -/
def nativePrimeCoordinateUnit (p : ProjectiveSpectrum 𝓑)
    (a : S) (hp : a ∉ p.asHomogeneousIdeal) :
    (Localization p.asHomogeneousIdeal.toIdeal.primeCompl)ˣ :=
  (IsLocalization.map_units (Localization p.asHomogeneousIdeal.toIdeal.primeCompl)
    (⟨a, hp⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)).unit

/-- Multiplication by the actual coordinate to an arbitrary integer power
on the original module localization. -/
def nativePrimeIntegerTwistEquiv (p : ProjectiveSpectrum 𝓑)
    (a : S) (hp : a ∉ p.asHomogeneousIdeal) (m : ℤ) :
    nativeProjectiveModuleAtPrime (D := S) 𝓑 p ≃ₗ[
      HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal]
      nativeProjectiveModuleAtPrime (D := S) 𝓑 p :=
  ((nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).trans
    ((nativePrimeCoordinateUnit 𝓑 p a hp ^ m).mulLeftLinearEquiv
      (HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal)
      (Localization p.asHomogeneousIdeal.toIdeal.primeCompl))).trans
    (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).symm

/-- This construction agrees with the previously proved positive twist. -/
theorem nativePrimeIntegerTwistEquiv_ofNat (p : ProjectiveSpectrum 𝓑)
    (a : S) (hp : a ∉ p.asHomogeneousIdeal) (n : ℕ) :
    nativePrimeIntegerTwistEquiv 𝓑 p a hp (n : ℤ) =
      nativeProjectivePrimeTwistEquiv 𝓑 p a hp n := by
  simp only [nativePrimeIntegerTwistEquiv, nativePrimeCoordinateUnit,
    Int.ofNat_eq_natCast, zpow_natCast, nativeProjectivePrimeTwistEquiv]

/-- Negative integer powers are the actual inverse positive twist. -/
theorem nativePrimeIntegerTwistEquiv_negSucc (p : ProjectiveSpectrum 𝓑)
    (a : S) (hp : a ∉ p.asHomogeneousIdeal) (n : ℕ) :
    nativePrimeIntegerTwistEquiv 𝓑 p a hp (Int.negSucc n) =
      (nativeProjectivePrimeTwistEquiv 𝓑 p a hp (n + 1)).symm := by
  ext f
  have h : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
  simp only [nativePrimeIntegerTwistEquiv, nativePrimeCoordinateUnit,
    h, zpow_neg, zpow_natCast, nativeProjectivePrimeTwistEquiv,
    LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, Units.symm_mulLeftLinearEquiv_apply,
    Units.mulLeftLinearEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The integer-power formula holds in the actual ring localization. -/
theorem nativePrimeIntegerTwistEquiv_localizedValue (p : ProjectiveSpectrum 𝓑)
    (a : S) (hp : a ∉ p.asHomogeneousIdeal) (m : ℤ)
    (f : nativeProjectiveModuleAtPrime (D := S) 𝓑 p) :
    nativeProjectiveRingModuleLocalizationEquiv 𝓑 p
      (nativePrimeIntegerTwistEquiv 𝓑 p a hp m f) =
      ((nativePrimeCoordinateUnit 𝓑 p a hp ^ m :
        (Localization p.asHomogeneousIdeal.toIdeal.primeCompl)ˣ) :
          Localization p.asHomogeneousIdeal.toIdeal.primeCompl) *
        nativeProjectiveRingModuleLocalizationEquiv 𝓑 p f := by
  simp only [nativePrimeIntegerTwistEquiv, LinearEquiv.trans_apply,
    Units.mulLeftLinearEquiv_apply, LinearEquiv.apply_symm_apply]

/-- Opposite integer powers cancel on the actual original module. -/
theorem nativePrimeIntegerTwistEquiv_neg_apply (p : ProjectiveSpectrum 𝓑)
    (a : S) (hp : a ∉ p.asHomogeneousIdeal) (m : ℤ)
    (f : nativeProjectiveModuleAtPrime (D := S) 𝓑 p) :
    nativePrimeIntegerTwistEquiv 𝓑 p a hp (-m)
      (nativePrimeIntegerTwistEquiv 𝓑 p a hp m f) = f := by
  apply (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).injective
  rw [nativePrimeIntegerTwistEquiv_localizedValue,
    nativePrimeIntegerTwistEquiv_localizedValue]
  simp only [zpow_neg, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]

/-- Integer coordinate multiplication preserves the actual locally
homogeneous-fraction condition, changing its degree by that integer. -/
theorem nativeIntegerTwistLocalFraction_forward (a : S) (ha : a ∈ 𝓑 1)
    (m l : ℤ) {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (hp : ∀ p : U, a ∉ p.1.asHomogeneousIdeal)
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := S) 𝓑 p.1}
    (hf : (nativeProjectiveModuleLocalPredicate 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑) l).pred f) :
    (nativeProjectiveModuleLocalPredicate 𝓑
      (nativeProjectiveRingIntegerPiece 𝓑) (l + m)).pred
      (fun p => nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hp p) m (f p)) := by
  cases m with
  | ofNat n =>
    simpa only [nativePrimeIntegerTwistEquiv_ofNat, Int.ofNat_eq_natCast] using
      nativeProjectiveTwistLocalFraction_forward 𝓑 a ha n l hp hf
  | negSucc n =>
    have h : l + Int.negSucc n + ((n + 1 : ℕ) : ℤ) = l := by omega
    have hf' : (nativeProjectiveModuleLocalPredicate 𝓑
        (nativeProjectiveRingIntegerPiece 𝓑)
        (l + Int.negSucc n + ((n + 1 : ℕ) : ℤ))).pred f := by
      simpa only [h] using hf
    simpa only [nativePrimeIntegerTwistEquiv_negSucc] using
      nativeProjectiveTwistLocalFraction_backward 𝓑 a ha (n + 1)
        (l + Int.negSucc n) hp hf'

end LinearStudy
