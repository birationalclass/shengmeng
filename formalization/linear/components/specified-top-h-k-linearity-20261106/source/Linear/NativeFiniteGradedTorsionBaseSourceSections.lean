module
public import Linear.NativeFiniteGradedTorsionChartSections
public import Linear.NativeBaseSourceBaseChartInjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable [IsDomain S] [IsNoetherianRing S] [Module.Finite S M]
variable {κ ι : Type u} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
variable (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
include c hc hgenC
/-- The actual source-side image-product charts are bijective for ALL finite
coefficients, including torsion; independent coordinates c generate the source. -/
theorem nativeFiniteGradedIndependentSourceCechProductSectionMap_bijective_general
    (a : ι → R) (ha : ∀ i,a i ∈ A 1) (p : ℕ) (t : Fin (p+1) → ι) :
    Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS (p+1)
      (algebraMap R S (∏ k : Fin (p+1),a (t k)))
      ((normalizationBaseGradedRingHom A B).map_mem (nativeProjective_cechProduct_mem_degree A a ha p t))) := by
  let b : ι → S := fun i => algebraMap R S (a i)
  have hb : ∀ i,b i ∈ B 1 := fun i => (normalizationBaseGradedRingHom A B).map_mem (ha i)
  have H := nativeFiniteGradedIndependentCechProductSectionMap_bijective_general B D hS c hc hgenC b hb p t
  have transport : ∀ (z : S) (hz : z ∈ B (p+1)),(∏ k : Fin (p+1),b (t k))=z →
      Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS (p+1) z hz) := by
    intro z hz h
    subst z
    exact H
  exact transport _ _ (map_prod (algebraMap R S) (fun k : Fin (p+1) => a (t k)) Finset.univ).symm
end LinearStudy
