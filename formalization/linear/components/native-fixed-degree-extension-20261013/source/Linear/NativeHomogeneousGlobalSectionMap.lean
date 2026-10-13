module
public import Linear.NativeProjectiveDegreeZeroMap
public import Linear.NativeHomogeneousGlobalSection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K S D E : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module K D] [Module S D]
variable [AddCommGroup E] [Module K E] [Module S E]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : D, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ)+d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → b • x ∈ ℰ ((n : ℤ)+d))

/-- The degree-preserving sheaf map takes the actual fraction ell/1
to the actual fraction b(ell)/1 at every ORIGINAL homogeneous prime. -/
theorem nativeHomogeneousGlobalSection_degreeZeroMap
    (b : D →ₗ[S] E) (hh : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d → b x ∈ ℰ d)
    (k : ℤ) (ell : 𝒟 k) :
    ((nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE b hh k).app ⊤)
      (nativeProjectiveModuleHomogeneousGlobalSection 𝓑 𝒟 hD k ell) =
      nativeProjectiveModuleHomogeneousGlobalSection 𝓑 ℰ hE k
        ⟨b ell,hh k ell ell.property⟩ := by
  apply Subtype.ext
  funext p
  exact nativeProjectiveModuleAtPrimeMap_mk 𝓑 b p.1 ell 1
end LinearStudy
