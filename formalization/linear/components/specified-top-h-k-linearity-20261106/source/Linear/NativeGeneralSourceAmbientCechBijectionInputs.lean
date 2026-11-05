module
public import Linear.NativeFiniteGradedTorsionBaseSourceSections
public import Linear.NativeFiniteGradedWeightedSectionsFunctionSurjective
public import Linear.NativeBaseSourceBaseChartInjective
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
attribute [local irreducible] nativeProjectiveModuleSections nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf
include c hc
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
attribute [local irreducible] nativeProjectiveChartDegreeZeroSectionMap
/-- Both actual original chart bijections,with the EXACT membership proofs
used by the original weighted coefficient comparison,derived for one finite
coefficient at a time. This is a proof of their conjunction,not a certificate. -/
theorem nativeIndependentSourceAmbientCechChartBijections_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι) :
    let z := ∏ l : Fin (p+1),a (t l)
    let hz := nativeProjective_cechProduct_mem_degree A a ha p t
    Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap A D hR (p+1) z hz) ∧
    Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS (p+1)
      (algebraMap R S z) ((normalizationBaseGradedRingHom A B).map_mem hz)) :=
  ⟨nativeFiniteGradedIndependentCechProductSectionMap_bijective_general A D hR a ha hgenR a ha p t,
   nativeFiniteGradedIndependentSourceCechProductSectionMap_bijective_general A B D hS c hc hgenC a ha p t⟩
end LinearStudy
