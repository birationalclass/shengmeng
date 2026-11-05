module
public import Linear.NativeProjectiveModuleSheafMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S D E : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable [AddCommGroup E] [Module S E] [Module K E]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : D, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ) + d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → b • x ∈ ℰ ((n : ℤ) + d))
variable (e : D →ₗ[S] E)
variable (hh : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d → e x ∈ ℰ d)
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- The actual degree-zero map on native sections, with the SAME integer
twist on both sides. This removes only the syntactic k+0 transport. -/
def nativeProjectiveDegreeZeroSectionMap (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    nativeProjectiveModuleSections 𝓑 𝒟 hD k U →ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 ℰ hE k U where
  toFun x := ⟨fun p => nativeProjectiveModuleAtPrimeMap 𝓑 e p.1 (x.1 p), by
    change (nativeProjectiveModuleLocalPredicate 𝓑 ℰ k).pred
      (fun p => nativeProjectiveModuleAtPrimeMap 𝓑 e p.1 (x.1 p))
    simpa only [add_zero] using nativeProjectiveModuleLocalPredicate_map
      𝓑 𝒟 ℰ 0 e (by simpa only [add_zero] using hh) k x.property⟩
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModuleAtPrimeMap 𝓑 e p.1).map_add _ _
  map_smul' r x := by
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModuleAtPrimeMap 𝓑 e p.1).map_smul (r.1 p) (x.1 p)

def nativeProjectiveDegreeZeroPresheafMap (k : ℤ) :
    nativeProjectiveModulePresheaf 𝓑 𝒟 hD k ⟶
      nativeProjectiveModulePresheaf 𝓑 ℰ hE k where
  app U := by
    letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hD k U
    letI := nativeProjectiveModuleSectionModule 𝓑 𝒟 hD k U
    letI := nativeProjectiveModuleSectionGroup 𝓑 ℰ hE k U
    letI := nativeProjectiveModuleSectionModule 𝓑 ℰ hE k U
    exact ModuleCat.ofHom (nativeProjectiveDegreeZeroSectionMap 𝓑 𝒟 ℰ hD hE e hh k U)
  naturality i := by
    apply ModuleCat.hom_ext
    rfl

/-- The genuine degree-preserving native sheaf map. -/
def nativeProjectiveDegreeZeroSheafMap (k : ℤ) :
    nativeProjectiveModuleSheaf 𝓑 𝒟 hD k ⟶
      nativeProjectiveModuleSheaf 𝓑 ℰ hE k where
  val := nativeProjectiveDegreeZeroPresheafMap 𝓑 𝒟 ℰ hD hE e hh k

theorem nativeProjectiveDegreeZeroSectionMap_injective
    (he : Function.Injective e) (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    Function.Injective (nativeProjectiveDegreeZeroSectionMap 𝓑 𝒟 ℰ hD hE e hh k U) := by
  intro x y hxy
  apply Subtype.ext
  funext p
  apply nativeProjectiveModuleAtPrimeMap_injective 𝓑 e he p.1
  exact congrArg (fun z => z.1 p) hxy

theorem nativeProjectiveDegreeZeroSheafMap_mono (he : Function.Injective e) (k : ℤ) :
    Mono (nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE e hh k) := by
  constructor
  intro Z g h hgh
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply nativeProjectiveDegreeZeroSectionMap_injective 𝓑 𝒟 ℰ hD hE e hh he k U
  exact congrArg (fun φ => (φ.val.app U) x) hgh

end LinearStudy
