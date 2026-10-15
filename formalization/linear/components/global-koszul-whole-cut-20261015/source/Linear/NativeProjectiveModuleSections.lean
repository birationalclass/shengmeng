module
public import Linear.NativeProjectiveModuleLocalSMul
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

/-- The actual local-fraction sections form a submodule under the
ACTUAL native Proj structure-ring action, on every open set. -/
def nativeProjectiveModuleSections (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    Submodule ((ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U)
      (∀ p : U.unop, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1) where
  carrier := {f | (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred f}
  zero_mem' := nativeProjectiveModuleLocalPredicate_zero 𝓑 𝒟 k U.unop
  add_mem' := fun ha hb => nativeProjectiveModuleLocalPredicate_add 𝓑 𝒟 hgrade k ha hb
  smul_mem' := fun r f hf =>
    nativeProjectiveModuleLocalPredicate_smul 𝓑 𝒟 hgrade k r.property hf

/-- Additive structure on the actual Type-valued associated-module
sheaf sections, inherited from their constructed submodule. -/
@[instance_reducible] def nativeProjectiveModuleSectionGroup (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    AddCommGroup ((nativeProjectiveModuleSheafInType 𝓑 𝒟 k).1.obj U) :=
  inferInstanceAs (AddCommGroup (nativeProjectiveModuleSections 𝓑 𝒟 hgrade k U))

/-- Actual structure-ring module structure on the associated-module
sheaf's original section type. The ring is mathlib's native Proj ring. -/
@[instance_reducible] def nativeProjectiveModuleSectionModule (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hgrade k U
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U)
      ((nativeProjectiveModuleSheafInType 𝓑 𝒟 k).1.obj U) := by
  letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hgrade k U
  exact inferInstanceAs (Module ((ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U)
    (nativeProjectiveModuleSections 𝓑 𝒟 hgrade k U))

end LinearStudy
