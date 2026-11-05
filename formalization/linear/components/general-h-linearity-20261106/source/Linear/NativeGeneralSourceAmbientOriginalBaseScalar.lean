module
public import Linear.NativeGeneralSourceAmbientCechSections
public import Linear.NativeGeneralSourceAmbientCechBijectionInputs
public import Linear.NativeWeightedSourceAmbientOriginalBaseScalar
public import Linear.NativeFiniteGradedIndependentCechSections
public import Linear.NativeFiniteGradedWeightedSectionsFunctionSurjective
public import Linear.NativeBaseSourceBaseChartInjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 5000
set_option diagnostics true
set_option diagnostics.threshold 100
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
include c hc
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
attribute [local irreducible] nativeIndependentSourceAmbientCechSectionAddEquiv_general
  nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf
  nativeWeightedSourceAmbientSectionAddEquiv
  nativeProjectiveModuleSections nativeProjectiveChartDegreeZeroSectionMap
/-- Original base-global scalar commutation for arbitrary finite graded
coefficients,including torsion,on every original finite product chart.
Both original local chart bijections are DERIVED here. -/
def nativeIndependentSourceAmbientCechSectionAddEquiv_originalBaseScalar_general_proof
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (p : ℕ) (t : Fin (p+1) → ι)
    (r : Γ(Spec (CommRingCat.of K),⊤))
    (s : nativeProjectiveModuleSections A D hR 0
      (op (Proj.basicOpen A (∏ j : Fin (p+1),a (t j))))) :=
  let z := ∏ j : Fin (p+1),a (t j)
  let hz := nativeProjective_cechProduct_mem_degree A a ha p t
  let hMaps := nativeIndependentSourceAmbientCechChartBijections_general A B D hR hS a ha c hc
    hgenR hgenC p t
  nativeWeightedSourceAmbientSectionAddEquiv_originalBaseScalar_proof A B D hR hS
    (p+1) z hz (Nat.succ_pos p) hMaps.1 hMaps.2 r s
end LinearStudy
