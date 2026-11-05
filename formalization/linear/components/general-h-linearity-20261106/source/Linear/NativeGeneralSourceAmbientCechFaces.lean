module
public import Linear.NativeFiniteGradedSourceAmbientCechFaces
public import Linear.NativeGeneralSourceAmbientCechSections
/- Arbitrary finite coefficients;the original fraction maps,ordered signs and actual-H objects are retained.Normalized dualizing trace remains OPEN. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K R M] [IsScalarTower K S M]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ c : R,c ∈ A n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ c : S,c ∈ B n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
variable [IsDomain R] [IsDomain S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite R M] [Module.Finite S M]
variable {ι : Type u} (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable {κ : Type u} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
include c hc ha hS
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv nativeProjectiveModuleSections nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf
/-- Actual proof term:EVERY actual deletion-face restriction commutes with the derived
source/ambient section equivalences.Not merely first/pairwise overlaps:
this holds for every p,every original tuple and every deleted coordinate. -/
def nativeIndependentSourceAmbientCechSectionAddEquiv_delete_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+2) → ι) (k : Fin (p+2))
    (s : nativeProjectiveModuleSections A D hR 0
      (op (Proj.basicOpen A (∏ j : Fin (p+1),a (t (k.succAbove j)))))) :=
  let small := ∏ j : Fin (p+1),a (t (k.succAbove j))
  let z := ∏ j : Fin (p+2),a (t j)
  let hsmall : small ∈ A (p+1) := nativeProjective_cechProduct_mem_degree A a ha p (fun j => t (k.succAbove j))
  let hz : z ∈ A (p+1+1) := nativeProjective_cechProduct_mem_degree A a ha (p+1) t
  let h0 := nativeFiniteGradedIndependentCechProductSectionMap_bijective_general A D hR a ha hgenR a ha p
    (fun j => t (k.succAbove j))
  let h1 := nativeFiniteGradedIndependentSourceCechProductSectionMap_bijective_general A B D hS c hc hgenC a ha p
    (fun j => t (k.succAbove j))
  let h2 := nativeFiniteGradedIndependentCechProductSectionMap_bijective_general A D hR a ha hgenR a ha (p+1) t
  let h3 := nativeFiniteGradedIndependentSourceCechProductSectionMap_bijective_general A B D hS c hc hgenC a ha (p+1) t
  nativeWeightedSourceAmbientSectionAddEquiv_overlap_named A B D hR hS (p+1) 1 small (a (t k)) z
    hsmall (ha (t k)) hz (nativeCechCoordinateProduct_delete_mul a p t k) h0 h1 h2 h3 s
end LinearStudy
