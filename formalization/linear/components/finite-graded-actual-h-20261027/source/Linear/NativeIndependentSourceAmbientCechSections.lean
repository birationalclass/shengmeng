module
public import Linear.NativeFiniteGradedIndependentCechSections
public import Linear.NativeFiniteGradedWeightedSectionsFunctionSurjective
public import Linear.NativeBaseSourceBaseChartInjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
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
variable [IsDomain S] [Module.IsTorsionFree S M]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite R M] [Module.Finite S M]
variable {ι : Type u} (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable {κ : Type u} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
include c hc
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
/-- On EVERY original coordinate intersection,the ACTUAL ambient and source
section groups of the SAME finite graded module are additively isomorphic.
The independent source coordinates c generate S;normalization coordinates
need not generate S.Only source torsion-freeness is used;the ambient module may have base torsion.
All section bijections are derived from the stated original algebraic data. -/
def nativeIndependentSourceAmbientCechSectionAddEquiv
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι) :
    nativeProjectiveModuleSections A D hR 0
      (op (Proj.basicOpen A (∏ k : Fin (p+1),a (t k)))) ≃+
      nativeProjectiveModuleSections B D hS 0
        (op (Proj.basicOpen B (algebraMap R S (∏ k : Fin (p+1),a (t k))))) := by
  let z := ∏ k : Fin (p+1),a (t k)
  have hz : z ∈ A (p+1) := nativeProjective_cechProduct_mem_degree A a ha p t
  have hA := nativeFiniteGradedAmbientCechProductSectionMap_bijective A B D hR a ha hgenR p t
  have hB := nativeFiniteGradedIndependentSourceCechProductSectionMap_bijective A B D hS c hc hgenC a ha p t
  exact nativeWeightedSourceAmbientSectionAddEquiv A B D hR hS (p+1) z hz hA hB
end LinearStudy
