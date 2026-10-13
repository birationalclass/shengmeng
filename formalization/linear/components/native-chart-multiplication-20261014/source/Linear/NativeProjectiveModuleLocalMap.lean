module
public import Linear.NativeProjectiveModuleSheaf
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
attribute [local instance] LocalizedModule.moduleOfIsLocalization
attribute [local instance] nativeProjectiveAtPrimeModuleScalar

/-- Localize the original linear map at the actual original homogeneous
prime and restrict its scalars to the native degree-zero local ring. -/
def nativeProjectiveModuleAtPrimeMap (e : D →ₗ[S] E)
    (p : ProjectiveSpectrum 𝓑) :
    nativeProjectiveModuleAtPrime (D := D) 𝓑 p →ₗ[
      HomogeneousLocalization.AtPrime 𝓑 p.asHomogeneousIdeal.toIdeal]
      nativeProjectiveModuleAtPrime (D := E) 𝓑 p := by
  let f := LocalizedModule.map p.asHomogeneousIdeal.toIdeal.primeCompl e
  exact {
    toFun := f
    map_add' := f.map_add
    map_smul' := fun z x => f.map_smul
      (algebraMap _ (Localization p.asHomogeneousIdeal.toIdeal.primeCompl) z) x }

theorem nativeProjectiveModuleAtPrimeMap_mk (e : D →ₗ[S] E)
    (p : ProjectiveSpectrum 𝓑) (ell : D)
    (b : p.asHomogeneousIdeal.toIdeal.primeCompl) :
    nativeProjectiveModuleAtPrimeMap 𝓑 e p (LocalizedModule.mk ell b) =
      LocalizedModule.mk (e ell) b :=
  LocalizedModule.map_mk _ e ell b

theorem nativeProjectiveModuleAtPrimeMap_injective (e : D →ₗ[S] E)
    (he : Function.Injective e) (p : ProjectiveSpectrum 𝓑) :
    Function.Injective (nativeProjectiveModuleAtPrimeMap 𝓑 e p) :=
  LocalizedModule.map_injective _ e he

variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E)
variable (δ : ℤ) (e : D →ₗ[S] E)
variable (hh : ∀ d : ℤ, ∀ ell : D, ell ∈ 𝒟 d → e ell ∈ ℰ (d+δ))
include hh

/-- An actual degree-δ homogeneous map sends local degree-k fractions
to actual degree-(k+δ) fractions on the SAME original open set. -/
theorem nativeProjectiveModuleFraction_map (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1}
    (hf : nativeProjectiveModuleIsFraction 𝓑 𝒟 k f) :
    nativeProjectiveModuleIsFraction 𝓑 ℰ (k+δ)
      (fun p => nativeProjectiveModuleAtPrimeMap 𝓑 e p.1 (f p)) := by
  rcases hf with ⟨n,ell,b,hb,hf⟩
  have hnum : e (ell : D) ∈ ℰ ((n : ℤ)+(k+δ)) := by
    simpa only [add_assoc] using hh ((n : ℤ)+k) ell ell.property
  refine ⟨n,⟨e (ell : D),hnum⟩,b,hb,?_⟩
  intro p
  dsimp only
  erw [hf]
  exact nativeProjectiveModuleAtPrimeMap_mk 𝓑 e p.1 ell ⟨b,hb p⟩

/-- Homogeneous maps preserve the locally homogeneous-fraction predicate
on the original Proj, without supplying any sheaf morphism as an input. -/
theorem nativeProjectiveModuleLocalPredicate_map (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1}
    (hf : (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred f) :
    (nativeProjectiveModuleLocalPredicate 𝓑 ℰ (k+δ)).pred
      (fun p => nativeProjectiveModuleAtPrimeMap 𝓑 e p.1 (f p)) := by
  intro p
  rcases hf p with ⟨V,hp,i,hf⟩
  refine ⟨V,hp,i,?_⟩
  exact nativeProjectiveModuleFraction_map 𝓑 𝒟 ℰ δ e hh k hf

end LinearStudy
