module
public import Linear.NativeProjectiveModuleSheafMap
public import Mathlib.LinearAlgebra.BilinearMap
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
attribute [local instance] nativeProjectiveAtPrimeModuleScalar
attribute [local instance] nativeProjectiveAmbientSectionModule

include hD in
/-- Actual scalar multiplication by a degree-n element is a degree-n
homogeneous linear map on the original module, with no freeness assumption. -/
theorem nativeProjectiveHomogeneousSMul_homogeneous
    (a : S) (n : ℕ) (ha : a ∈ 𝓑 n) :
    ∀ d : ℤ, ∀ ell : M, ell ∈ 𝒟 d →
      (LinearMap.lsmul S M a) ell ∈ 𝒟 (d+(n : ℤ)) := by
  intro d ell hell
  simpa only [LinearMap.lsmul_apply, add_comm] using hD n d a ha ell hell

/-- The induced map uses the same actual localized scalar action. -/
theorem nativeProjectiveHomogeneousSMul_prime_value
    (a : S) (p : ProjectiveSpectrum 𝓑)
    (x : nativeProjectiveModuleAtPrime (D := M) 𝓑 p) :
    nativeProjectiveModuleAtPrimeMap 𝓑 (LinearMap.lsmul S M a) p x = a • x := by
  induction x using LocalizedModule.induction_on with
  | _ ell b =>
    rw [nativeProjectiveModuleAtPrimeMap_mk, LinearMap.lsmul_apply,
      LocalizedModule.smul'_mk]

/-- A global morphism of the actual native module sheaves, constructed
from homogeneous scalar multiplication on the original module. -/
def nativeProjectiveHomogeneousSMul
    (a : S) (n : ℕ) (ha : a ∈ 𝓑 n) (k : ℤ) :
    nativeProjectiveModuleSheaf 𝓑 𝒟 hD k ⟶
      nativeProjectiveModuleSheaf 𝓑 𝒟 hD (k+(n : ℤ)) :=
  nativeProjectiveModuleSheafMap 𝓑 𝒟 𝒟 hD hD (n : ℤ)
    (LinearMap.lsmul S M a)
    (nativeProjectiveHomogeneousSMul_homogeneous 𝓑 𝒟 hD a n ha) k

/-- On every original open, the constructed morphism multiplies every
prime-localized value by the original scalar a. -/
theorem nativeProjectiveHomogeneousSMul_section_value
    (a : S) (n : ℕ) (ha : a ∈ 𝓑 n) (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (s : nativeProjectiveModuleSections 𝓑 𝒟 hD k U) (p : U.unop) :
    ((nativeProjectiveHomogeneousSMul 𝓑 𝒟 hD a n ha k).val.app U s).1 p =
      a • s.1 p := by
  exact nativeProjectiveHomogeneousSMul_prime_value 𝓑 a p.1 (s.1 p)

end LinearStudy
