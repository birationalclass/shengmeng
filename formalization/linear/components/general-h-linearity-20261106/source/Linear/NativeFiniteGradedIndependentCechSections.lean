module
public import Linear.NativeFiniteGradedSourceAmbientCechSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
section Source
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hD : ∀ n : ℕ,∀ d : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D d → z • x ∈ D ((n : ℤ)+d))
variable [IsNoetherianRing S] [Module.Finite S M]
variable {κ ι : Type u} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
variable (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
include c hc hgenC
/-- The target chart coordinates b need NOT generate the source ring.
Surjectivity is derived using an INDEPENDENT generating family c of the
original source ring,while each b-product retains its true degree p+1. -/
theorem nativeFiniteGradedIndependentCechProductSectionMap_surjective
    (b : ι → S) (hb : ∀ i,b i ∈ B 1) (p : ℕ) (t : Fin (p+1) → ι) :
    Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap B D hD (p+1)
      (∏ k : Fin (p+1),b (t k)) (nativeProjective_cechProduct_mem_degree B b hb p t)) := by
  have transport (d e : ℕ) (x y : S) (hx : x ∈ B d) (hy : y ∈ B e)
      (hd : d=e) (hxy : x=y)
      (hs : Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap B D hD d x hx)) :
      Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap B D hD e y hy) := by
    cases hd
    cases hxy
    exact hs
  cases p with
  | zero =>
    exact transport 1 (0+1) (b (t 0)) _ (hb (t 0)) _ rfl
      (Fin.prod_univ_one (fun k : Fin (0+1) => b (t k))).symm
      (nativeFiniteGradedChartDegreeZeroSectionMap_surjective B D hD c hc hgenC (b (t 0)) (hb (t 0)))
  | succ p =>
    let z := ∏ k : Fin (p+1),b (t k.succ)
    have hz : z ∈ B (p+1) := nativeProjective_cechProduct_mem_degree B b hb p (fun k => t k.succ)
    have H := nativeFiniteGradedWeightedChartSectionMap_surjective B D hD c hc hgenC
      (p+1) (Nat.zero_lt_succ p) (b (t 0)) z (hb (t 0)) hz
    exact transport (1+(p+1)) (p+1+1) (b (t 0)*z) _
      (SetLike.mul_mem_graded (hb (t 0)) hz) _ (by omega)
      (Fin.prod_univ_succ (fun k : Fin (p+1+1) => b (t k))).symm H
end Source
section BaseSource
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K R M] [IsScalarTower K S M]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n : ℤ)+j))
variable [IsDomain S] [Module.IsTorsionFree S M] [IsNoetherianRing S] [Module.Finite S M]
variable {κ ι : Type u} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
variable (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
include c hc hgenC
variable (a : ι → R) (ha : ∀ i,a i ∈ A 1)
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
/-- Actual source chart bijectivity for arbitrary base-coordinate products.
Only the SOURCE'S OWN coordinates c generate S;the normalization coordinates
are never assumed to generate S as an algebra. -/
theorem nativeFiniteGradedIndependentSourceCechProductSectionMap_bijective
    (p : ℕ) (t : Fin (p+1) → ι) :
    Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS (p+1)
      (algebraMap R S (∏ k : Fin (p+1),a (t k)))
      ((normalizationBaseGradedRingHom A B).map_mem (nativeProjective_cechProduct_mem_degree A a ha p t))) := by
  let b := fun i => algebraMap R S (a i)
  have hb : ∀ i,b i ∈ B 1 := fun i => (normalizationBaseGradedRingHom A B).map_mem (ha i)
  let z := ∏ k : Fin (p+1),b (t k)
  have H := nativeFiniteGradedIndependentCechProductSectionMap_surjective B D hS c hc hgenC b hb p t
  constructor
  · exact nativeProjectiveChartDegreeZeroSectionMap_injective_all B D hS (p+1)
      (Nat.zero_lt_succ p) _ _
  · have transport : ∀ (y : S) (hy : y ∈ B (p+1)),z=y →
        Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap B D hS (p+1) y hy) := by
      intro y hy h
      subst y
      exact H
    exact transport _ _ (map_prod (algebraMap R S) (fun k : Fin (p+1) => a (t k)) Finset.univ).symm
end BaseSource
end LinearStudy
