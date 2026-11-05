module
public import Linear.NativeWeightedSourceAmbientSectionEquiv
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
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
include B in
/-- The ACTUAL ambient section map is bijective on every coordinate product.
Its injectivity uses torsion-freeness over the source,not over the base ring. -/
theorem nativeFiniteGradedAmbientCechProductSectionMap_bijective
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι) :
    Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap A D hR (p+1)
      (∏ k : Fin (p+1),a (t k)) (nativeProjective_cechProduct_mem_degree A a ha p t)) :=
  ⟨nativeBaseSourceBaseChartDegreeZeroSectionMap_injective A B D hR (p+1)
    (Nat.zero_lt_succ p) _ _,
    nativeFiniteGradedCechProductChartSectionMap_surjective A D hR a ha hgenR p t⟩
/-- Actual source chart bijectivity on EVERY coordinate product image.It is
DERIVED from the finite graded source module,not supplied as a section input. -/
theorem nativeFiniteGradedSourceCechProductSectionMap_bijective
    (hgenS : Algebra.adjoin K (Set.range (fun i => algebraMap R S (a i))) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι) :
    Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS (p+1)
      (algebraMap R S (∏ k : Fin (p+1),a (t k)))
      ((normalizationBaseGradedRingHom A B).map_mem (nativeProjective_cechProduct_mem_degree A a ha p t))) := by
  let c := ∏ k : Fin (p+1),algebraMap R S (a (t k))
  have hc : c ∈ B (p+1) := nativeProjective_cechProduct_mem_degree B
    (fun i => algebraMap R S (a i)) (fun i => (normalizationBaseGradedRingHom A B).map_mem (ha i)) p t
  have H := nativeFiniteGradedCechProductChartSectionMap_surjective B D hS
    (fun i => algebraMap R S (a i)) (fun i => (normalizationBaseGradedRingHom A B).map_mem (ha i)) hgenS p t
  constructor
  · exact nativeProjectiveChartDegreeZeroSectionMap_injective_all B D hS (p+1)
      (Nat.zero_lt_succ p) _ _
  · have transport : ∀ (z : S) (hz : z ∈ B (p+1)),c=z →
        Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap B D hS (p+1) z hz) := by
      intro z hz h
      subst z
      exact H
    exact transport _ _ (map_prod (algebraMap R S) (fun k : Fin (p+1) => a (t k)) Finset.univ).symm
/-- On EVERY original coordinate intersection,the ACTUAL ambient and source
section groups of the SAME finite graded module are additively isomorphic.
Only source torsion-freeness is used;the ambient module may have base torsion.
All section bijections are derived from the stated original algebraic data. -/
def nativeFiniteGradedSourceAmbientCechSectionAddEquiv
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenS : Algebra.adjoin K (Set.range (fun i => algebraMap R S (a i))) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι) :
    nativeProjectiveModuleSections A D hR 0
      (op (Proj.basicOpen A (∏ k : Fin (p+1),a (t k)))) ≃+
      nativeProjectiveModuleSections B D hS 0
        (op (Proj.basicOpen B (algebraMap R S (∏ k : Fin (p+1),a (t k))))) := by
  let z := ∏ k : Fin (p+1),a (t k)
  have hz : z ∈ A (p+1) := nativeProjective_cechProduct_mem_degree A a ha p t
  have hA := nativeFiniteGradedAmbientCechProductSectionMap_bijective A B D hR a ha hgenR p t
  have hB := nativeFiniteGradedSourceCechProductSectionMap_bijective A B D hS a ha hgenS p t
  exact nativeWeightedSourceAmbientSectionAddEquiv A B D hR hS (p+1) z hz hA hB
end LinearStudy
