module
public import Linear.NativeGeneralNormalizationModuleHComparison
public import Linear.NativeProjectiveModuleCechHomologyObjects
public import Linear.FiniteNormalizationCoordinateCover
public import Linear.OrderedModuleCechActualAbelianHomology
public import Linear.NativeProjectiveTwistFinitePresentation
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
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K R M] [IsScalarTower K S M]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n : ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n : ℤ)+j))
variable [IsDomain R] [IsDomain S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite R S] [Module.Finite R M] [Module.Finite S M]
variable {ι κ : Type u} [LinearOrder ι] [Finite ι]
variable (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable (c : κ → S) (hc : ∀ i,c i ∈ B 1)
attribute [local irreducible] nativeProjectiveModuleSheaf schemeModuleToActualAbelianSheaf
  nativeIndependentFiniteNormalization_actualHigherHIso_general orderedModuleCechActualAbelianHomologyIso
/-- Exact original module-Cech/actual-H factorization,with the SAME
forgetting iso and SAME actual-H map; no whole comparison is replaced. -/
theorem nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_factorization_general
    {Y : Scheme.{u}} (pi : Proj A ⟶ Y)
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ) :
    nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general A B D hR hS a ha c hc pi hgenR hgenC k q =
      nativeProjectiveOrderedModuleCechHomologyIso A D hR pi a k (q+1) ≪≫
      nativeIndependentFiniteNormalization_actualHigherHIso_general A B D hR hS a ha c hc hgenR hgenC k q := rfl
end LinearStudy
