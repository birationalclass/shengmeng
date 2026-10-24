module
public import Linear.NativeProjectiveModuleSheafMap
public import Linear.NativeHomogeneousGlobalSectionMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S D E : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable [AddCommGroup E] [Module S E] [Module K E]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : E, ell ∈ ℰ d → b • ell ∈ ℰ ((n : ℤ)+d))
variable (δ : ℤ) (e : D →ₗ[S] E)
variable (hh : ∀ d : ℤ, ∀ ell : D, ell ∈ 𝒟 d → e ell ∈ ℰ (d+δ))
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- Extend the existing degree-zero section formula to the ACTUAL
homogeneous degree-delta embedding needed for the SAME original Q.
The equality uses original prime localization,with no comparison input. -/
theorem nativeProjectiveModuleSheafMap_homogeneousGlobalSection
    (k : ℤ) (ell : 𝒟 k) :
    (nativeProjectiveModuleSheafMap 𝓑 𝒟 ℰ hD hE δ e hh k).app ⊤
      (nativeProjectiveModuleHomogeneousGlobalSection 𝓑 𝒟 hD k ell) =
    nativeProjectiveModuleHomogeneousGlobalSection 𝓑 ℰ hE (k+δ)
      ⟨e (ell:D),hh k ell ell.property⟩ := by
  apply Subtype.ext
  funext p
  exact nativeProjectiveModuleAtPrimeMap_mk 𝓑 e p.1 ell 1
end LinearStudy
