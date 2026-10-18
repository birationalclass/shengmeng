module
public import Linear.NativeStructureModuleSheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local instance] LocalizedModule.moduleOfIsLocalization
attribute [local instance] nativeProjectiveAtPrimeModuleScalar

/-- Multiplication by a^m on the actual original ring-module localization
is an equivalence wherever a is nonvanishing, with the native homogeneous
local-ring action. This constructs the local twist trivialization. -/
def nativeProjectivePrimeTwistEquiv (p : ProjectiveSpectrum 𝓑)
    (a : S) (ha : a ∉ p.asHomogeneousIdeal) (m : ℕ) :
    nativeProjectiveModuleAtPrime (D := S) 𝓑 p ≃ₗ[
      HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal]
      nativeProjectiveModuleAtPrime (D := S) 𝓑 p := by
  let T := Localization p.asHomogeneousIdeal.toIdeal.primeCompl
  let H := HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal
  let u : Tˣ := (IsLocalization.map_units T
    (⟨a,ha⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)).unit ^ m
  let E := nativeProjectiveRingModuleLocalizationEquiv 𝓑 p
  exact (E.trans (u.mulLeftLinearEquiv H T)).trans E.symm

theorem nativeProjectivePrimeTwistEquiv_mk
    (p : ProjectiveSpectrum 𝓑) (a : S) (ha : a ∉ p.asHomogeneousIdeal) (m : ℕ)
    (ell : S) (b : p.asHomogeneousIdeal.toIdeal.primeCompl) :
    nativeProjectivePrimeTwistEquiv 𝓑 p a ha m (LocalizedModule.mk ell b) =
      LocalizedModule.mk (a^m*ell) b := by
  apply (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).injective
  change (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p)
    ((nativeProjectiveRingModuleLocalizationEquiv 𝓑 p).symm
      (_ * (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p)
        (LocalizedModule.mk ell b))) = _
  rw [LinearEquiv.apply_symm_apply,nativeProjectiveRingModuleLocalizationEquiv_mk,
    nativeProjectiveRingModuleLocalizationEquiv_mk]
  simp only [Units.val_pow_eq_pow_val,IsUnit.unit_spec,← map_pow]
  exact IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _

/-- The inverse twist chart formula divides by a^m using an ACTUAL
allowed denominator; it is not an abstract supplied trivialization. -/
theorem nativeProjectivePrimeTwistEquiv_symm_mk
    (p : ProjectiveSpectrum 𝓑) (a : S) (ha : a ∉ p.asHomogeneousIdeal) (m : ℕ)
    (ell : S) (b : p.asHomogeneousIdeal.toIdeal.primeCompl) :
    (nativeProjectivePrimeTwistEquiv 𝓑 p a ha m).symm (LocalizedModule.mk ell b) =
      LocalizedModule.mk ell (b * (⟨a,ha⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)^m) := by
  apply (nativeProjectivePrimeTwistEquiv 𝓑 p a ha m).injective
  rw [LinearEquiv.apply_symm_apply,nativeProjectivePrimeTwistEquiv_mk]
  exact (LocalizedModule.mk_cancel_common_right b
    ((⟨a,ha⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)^m) ell).symm

end LinearStudy
