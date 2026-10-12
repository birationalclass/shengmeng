module
public import Linear.NativeProjectiveModuleTwistPairingFraction
public import Mathlib.LinearAlgebra.TensorProduct.Basic
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
variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : M, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
attribute [local instance] LocalizedModule.smulOfIsLocalization
attribute [local instance] LocalizedModule.moduleOfIsLocalization
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- The genuine fraction pairing is bilinear over the actual native
structure-ring sections on every original open. -/
def nativeProjectiveModuleTwistPairing (m : ℕ) (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ) U →ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 𝒟 hD k U →ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 𝒟 hD (k+(m : ℤ)) U where
  toFun r := {
    toFun ell := ⟨fun p => nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1 (r.1 p) • ell.1 p,
      nativeProjectiveModuleTwistPairing_local 𝓑 𝒟 hD m k r.property ell.property⟩
    map_add' x y := by
      apply Subtype.ext
      funext p
      exact smul_add _ _ _
    map_smul' c ell := by
      apply Subtype.ext
      funext p
      change nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1 (r.1 p) •
        ((c.1 p).val • ell.1 p) =
        (c.1 p).val • (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1 (r.1 p) • ell.1 p)
      exact smul_comm _ _ _ }
  map_add' r t := by
    apply LinearMap.ext
    intro ell
    apply Subtype.ext
    funext p
    change nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1 (r.1 p+t.1 p) • ell.1 p = _
    rw [LinearEquiv.map_add, add_smul]
    rfl
  map_smul' c r := by
    apply LinearMap.ext
    intro ell
    apply Subtype.ext
    funext p
    change nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1 ((c.1 p) • r.1 p) • ell.1 p = _
    rw [LinearEquiv.map_smul]
    change ((c.1 p).val * nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1 (r.1 p)) • ell.1 p =
      (c.1 p).val • (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1 (r.1 p) • ell.1 p)
    exact mul_smul _ _ _

/-- The bilinear pairing keeps the original prime-localized value. -/
theorem nativeProjectiveModuleTwistPairing_value (m : ℕ) (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (r : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ) U)
    (ell : nativeProjectiveModuleSections 𝓑 𝒟 hD k U) (p : U.unop) :
    (nativeProjectiveModuleTwistPairing 𝓑 𝒟 hD m k U r ell).1 p =
      nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1 (r.1 p) • ell.1 p := rfl

/-- The actual pairing commutes with all original open restrictions. -/
theorem nativeProjectiveModuleTwistPairing_restrict (m : ℕ) (k : ℤ)
    {U V : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ} (i : U ⟶ V)
    (r : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ) U)
    (ell : nativeProjectiveModuleSections 𝓑 𝒟 hD k U) :
    (nativeProjectiveModulePresheaf 𝓑 𝒟 hD (k+(m : ℤ))).map i
      (nativeProjectiveModuleTwistPairing 𝓑 𝒟 hD m k U r ell) =
    nativeProjectiveModuleTwistPairing 𝓑 𝒟 hD m k V
      ((nativeProjectiveModulePresheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ)).map i r)
      ((nativeProjectiveModulePresheaf 𝓑 𝒟 hD k).map i ell) := by
  apply Subtype.ext
  funext p
  rfl

end LinearStudy
