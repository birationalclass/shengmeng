module
public import Linear.NativeProjectiveHomogeneousSMul
public import Mathlib.Algebra.Module.Equiv.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module S M] [Module K M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local instance] LocalizedModule.moduleOfIsLocalization
attribute [local instance] nativeProjectiveAtPrimeModuleScalar

/-- Multiplication by the actual unit a^m in the original prime localization
trivializes twists for an arbitrary module M, using its original ring action. -/
def nativeProjectiveModulePrimeTwistEquiv (p : ProjectiveSpectrum 𝓑)
    (a : S) (ha : a ∉ p.asHomogeneousIdeal) (m : ℕ) :
    nativeProjectiveModuleAtPrime (D := M) 𝓑 p ≃ₗ[
      HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal]
      nativeProjectiveModuleAtPrime (D := M) 𝓑 p := by
  let T := Localization p.asHomogeneousIdeal.toIdeal.primeCompl
  let H := HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal
  let u : Tˣ := (IsLocalization.map_units T
    (⟨a,ha⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)).unit ^ m
  exact {
    toFun := fun x => (u : T) • x
    invFun := fun x => ((u⁻¹ : Tˣ) : T) • x
    left_inv := fun x => inv_smul_smul u x
    right_inv := fun x => smul_inv_smul u x
    map_add' := fun x y => smul_add (u : T) x y
    map_smul' := fun c x => by
      change (u : T) • (algebraMap H T c • x) =
        algebraMap H T c • ((u : T) • x)
      exact smul_comm _ _ _ }

/-- The actual forward fraction formula keeps the denominator unchanged. -/
theorem nativeProjectiveModulePrimeTwistEquiv_mk
    (p : ProjectiveSpectrum 𝓑) (a : S) (ha : a ∉ p.asHomogeneousIdeal) (m : ℕ)
    (ell : M) (b : p.asHomogeneousIdeal.toIdeal.primeCompl) :
    nativeProjectiveModulePrimeTwistEquiv 𝓑 p a ha m (LocalizedModule.mk ell b) =
      LocalizedModule.mk (a^m • ell) b := by
  change (((IsLocalization.map_units
    (Localization p.asHomogeneousIdeal.toIdeal.primeCompl)
      (⟨a,ha⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)).unit ^ m :
        (Localization p.asHomogeneousIdeal.toIdeal.primeCompl)ˣ) :
        Localization p.asHomogeneousIdeal.toIdeal.primeCompl) •
    LocalizedModule.mk ell b = _
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow,
    algebraMap_smul, LocalizedModule.smul'_mk]

/-- The inverse uses the genuine allowed denominator b*a^m. -/
theorem nativeProjectiveModulePrimeTwistEquiv_symm_mk
    (p : ProjectiveSpectrum 𝓑) (a : S) (ha : a ∉ p.asHomogeneousIdeal) (m : ℕ)
    (ell : M) (b : p.asHomogeneousIdeal.toIdeal.primeCompl) :
    (nativeProjectiveModulePrimeTwistEquiv 𝓑 p a ha m).symm
      (LocalizedModule.mk ell b) =
      LocalizedModule.mk ell (b * (⟨a,ha⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)^m) := by
  apply (nativeProjectiveModulePrimeTwistEquiv 𝓑 p a ha m).injective
  rw [LinearEquiv.apply_symm_apply, nativeProjectiveModulePrimeTwistEquiv_mk]
  exact (LocalizedModule.mk_cancel_common_right b
    ((⟨a,ha⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)^m) ell).symm

end LinearStudy
