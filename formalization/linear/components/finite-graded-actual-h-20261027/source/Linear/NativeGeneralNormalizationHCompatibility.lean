module
public import Linear.NativeGeneralSourceAmbientComparisonCompatibility
public import Linear.NativeGeneralNormalizationModuleHComparison
public import Linear.NativeNormalizationCachedFactorization
public import Linear.NativeGeneralActualHCompatibility
public import Linear.NativeIndependentNormalizationHFactorization
public import Linear.FiniteNormalizationCoordinateCover
public import Linear.NativeSourceActualHCachedComparison
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
variable [Module.IsTorsionFree S M]
attribute [local irreducible] nativeProjectiveModuleSheaf schemeModuleToActualAbelianSheaf
  finiteTypeNativeProj_orderedActualHigherHIso
  nativeFiniteGradedTwist_cachedActualHigherHIso
  nativeIndependentSourceAmbientOrderedTwistCechIso
  nativeIndependentFiniteNormalization_moduleCechActualHigherHIso
/-- The general module-valued comparison uses EXACTLY the two original
specified factors. The original full-name raw-object equality is a separate
interface obligation,not claimed by this factored statement. -/
theorem nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general_eq_original_factors
    {Y : Scheme.{u}} (pi : Proj A ⟶ Y)
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ) :
    nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general A B D hR hS a ha c hc pi hgenR hgenC k q =
      orderedModuleCechActualAbelianHomologyIso pi (nativeProjectiveModuleSheaf A D hR k)
        (fun i => Proj.basicOpen A (a i)) (q+1) ≪≫
      nativeIndependentFiniteNormalization_cachedActualHigherHIso A B D hR hS a ha c hc hgenR hgenC k q :=
  congrArg
    (fun e : nativeProjectiveOrderedCechHomologyObject A D hR a k (q+1) ≅
        schemeModuleActualHObject (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1) =>
      orderedModuleCechActualAbelianHomologyIso pi (nativeProjectiveModuleSheaf A D hR k)
        (fun i => Proj.basicOpen A (a i)) (q+1) ≪≫ e)
    (nativeIndependentFiniteNormalization_actualHigherHIso_general_eq_cached_original A B D hR hS a ha c hc hgenR hgenC k q)
end LinearStudy
