module
public import Linear.NativeIndependentSourceAmbientCechSections
public import Linear.NativeWeightedSourceAmbientSectionScalar
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
/-- On every actual finite-coordinate product chart, the SAME existing
ambient/source section comparison commutes with actual homogeneous-chart
scalars. Both local section bijections are DERIVED. Source coordinates c,
not the normalization coordinate images, generate the source algebra. -/
theorem nativeIndependentSourceAmbientCechSectionAddEquiv_smul
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι)
    (r : HomogeneousLocalization.Away A (∏ k : Fin (p+1),a (t k)))
    (s : nativeProjectiveModuleSections A D hR 0
      (op (Proj.basicOpen A (∏ k : Fin (p+1),a (t k))))) :
    nativeIndependentSourceAmbientCechSectionAddEquiv A B D hR hS a ha c hc
      hgenR hgenC p t
      ((Proj.awayToSection A (∏ k : Fin (p+1),a (t k))).hom r • s) =
    ((Proj.awayToSection B (algebraMap R S (∏ k : Fin (p+1),a (t k)))).hom.comp
      (normalizationHomogeneousChartMap A B (∏ k : Fin (p+1),a (t k)))) r •
        nativeIndependentSourceAmbientCechSectionAddEquiv A B D hR hS a ha c hc
          hgenR hgenC p t s := by
  let z := ∏ k : Fin (p+1),a (t k)
  have hz : z ∈ A (p+1) := nativeProjective_cechProduct_mem_degree A a ha p t
  have hA := nativeFiniteGradedAmbientCechProductSectionMap_bijective A B D hR a ha hgenR p t
  have hB := nativeFiniteGradedIndependentSourceCechProductSectionMap_bijective A B D hS c hc hgenC a ha p t
  exact nativeWeightedSourceAmbientSectionAddEquiv_smul A B D hR hS
    (p+1) z hz hA hB r s
end LinearStudy
