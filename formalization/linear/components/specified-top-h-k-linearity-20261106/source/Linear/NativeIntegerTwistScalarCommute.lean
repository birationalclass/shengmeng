module
public import Linear.NativeIntegerPrimeTwist
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

theorem nativeRingLocalization_original_smul (p : ProjectiveSpectrum 𝓑)
    (a : S) (x : nativeProjectiveModuleAtPrime (D := S) 𝓑 p) :
    nativeProjectiveRingModuleLocalizationEquiv 𝓑 p (a • x) =
      algebraMap S (Localization p.asHomogeneousIdeal.toIdeal.primeCompl) a *
        nativeProjectiveRingModuleLocalizationEquiv 𝓑 p x := by
  induction x using LocalizedModule.induction_on with
  | _ z b =>
    rw [LocalizedModule.smul'_mk, nativeProjectiveRingModuleLocalizationEquiv_mk,
      nativeProjectiveRingModuleLocalizationEquiv_mk]
    exact (IsLocalization.mul_mk'_eq_mk'_of_mul a z b).symm

/-- The native integer coordinate frame commutes with actual original-ring
scalar multiplication, before any Laurent-coordinate transport. -/
theorem nativePrimeIntegerTwistEquiv_original_smul (p : ProjectiveSpectrum 𝓑)
    (a : S) (ha : a ∉ p.asHomogeneousIdeal) (k : ℤ) (c : S)
    (x : nativeProjectiveModuleAtPrime (D := S) 𝓑 p) :
    nativePrimeIntegerTwistEquiv 𝓑 p a ha k (c • x) =
      c • nativePrimeIntegerTwistEquiv 𝓑 p a ha k x := by
  apply (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).injective
  rw [nativePrimeIntegerTwistEquiv_localizedValue, nativeRingLocalization_original_smul,
    nativeRingLocalization_original_smul, nativePrimeIntegerTwistEquiv_localizedValue]
  exact mul_left_comm _ _ _
end LinearStudy
