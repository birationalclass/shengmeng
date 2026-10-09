module
public import Linear.NativeProjectiveModuleLocalMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
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

/-- The actual homogeneous map on sections over EVERY original open,
linear for the original native Proj structure-ring action. -/
def nativeProjectiveModuleSectionMap (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    nativeProjectiveModuleSections 𝓑 𝒟 hD k U →ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 ℰ hE (k+δ) U where
  toFun x := ⟨fun p => nativeProjectiveModuleAtPrimeMap 𝓑 e p.1 (x.1 p),
    nativeProjectiveModuleLocalPredicate_map 𝓑 𝒟 ℰ δ e hh k x.property⟩
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModuleAtPrimeMap 𝓑 e p.1).map_add _ _
  map_smul' r x := by
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModuleAtPrimeMap 𝓑 e p.1).map_smul (r.1 p) (x.1 p)

theorem nativeProjectiveModuleSectionMap_injective (he : Function.Injective e)
    (k : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    Function.Injective (nativeProjectiveModuleSectionMap 𝓑 𝒟 ℰ hD hE δ e hh k U) := by
  intro x y hxy
  apply Subtype.ext
  funext p
  apply nativeProjectiveModuleAtPrimeMap_injective 𝓑 e he p.1
  exact congrArg (fun z => z.1 p) hxy

/-- Global natural morphism of ACTUAL presheaves of modules on native Proj,
constructed by original-prime localization of the homogeneous map. -/
def nativeProjectiveModulePresheafMap (k : ℤ) :
    nativeProjectiveModulePresheaf 𝓑 𝒟 hD k ⟶
      nativeProjectiveModulePresheaf 𝓑 ℰ hE (k+δ) where
  app U := by
    letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hD k U
    letI := nativeProjectiveModuleSectionModule 𝓑 𝒟 hD k U
    letI := nativeProjectiveModuleSectionGroup 𝓑 ℰ hE (k+δ) U
    letI := nativeProjectiveModuleSectionModule 𝓑 ℰ hE (k+δ) U
    exact ModuleCat.ofHom (nativeProjectiveModuleSectionMap 𝓑 𝒟 ℰ hD hE δ e hh k U)
  naturality i := by
    apply ModuleCat.hom_ext
    rfl

/-- Global morphism of the constructed native associated-module SHEAVES,
with naturality and structure-ring linearity proved above. -/
def nativeProjectiveModuleSheafMap (k : ℤ) :
    nativeProjectiveModuleSheaf 𝓑 𝒟 hD k ⟶
      nativeProjectiveModuleSheaf 𝓑 ℰ hE (k+δ) where
  val := nativeProjectiveModulePresheafMap 𝓑 𝒟 ℰ hD hE δ e hh k

/-- Actual injective homogeneous module maps induce a MONOMORPHISM
of the actual sheaves on the ORIGINAL Proj scheme. -/
theorem nativeProjectiveModuleSheafMap_mono (he : Function.Injective e) (k : ℤ) :
    Mono (nativeProjectiveModuleSheafMap 𝓑 𝒟 ℰ hD hE δ e hh k) := by
  constructor
  intro Z g h hgh
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply nativeProjectiveModuleSectionMap_injective 𝓑 𝒟 ℰ hD hE δ e hh he k U
  exact congrArg (fun φ => (φ.val.app U) x) hgh

end LinearStudy
