module
public import Linear.NativeProjectiveModuleSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
variable {K S D : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D)
variable (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- The ORIGINAL native structure-ring action on the ORIGINAL section
submodule, with both carrier types fixed before typeclass elaboration. -/
def nativeProjectiveModuleScalarApply (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U)
    (s : nativeProjectiveModuleSections 𝓑 𝒟 hgrade k U) :
    nativeProjectiveModuleSections 𝓑 𝒟 hgrade k U :=
  @SMul.smul ((ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U)
    (nativeProjectiveModuleSections 𝓑 𝒟 hgrade k U) inferInstance r s
end LinearStudy
