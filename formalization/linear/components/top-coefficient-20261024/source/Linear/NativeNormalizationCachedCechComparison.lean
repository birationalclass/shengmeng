module
public import Linear.NativeIndependentSourceAmbientOrderedTwistCechCoefficient
public import Linear.NativeIndependentNormalizationActualHFactorization
public import Linear.CategoricalComparisonCoefficientFactorization
public import Linear.NativeProjectiveCechHomologyObjects
public import Linear.NativeIndependentSourceAmbientCechHomologyCoefficient
public import Linear.NativeFiniteGradedSourceActualHCoefficient
public import Linear.NativeProjActualHCoefficientNaturality
public import Linear.NativeProjectiveTwistQuasicoherent
public import Linear.FiniteNormalizationCoordinateCover
public import Linear.NativeProjActualHComparison
public import Linear.NativeProjectiveTwistFinitePresentation
public import Linear.NativeIndependentSourceAmbientOrderedTwistCech
public import Linear.NativeOrderedCechRegradingCoefficient
public import Linear.NativeIndependentSourceAmbientOrderedCech
public import Linear.OrderedFreeSheafHomCoefficientNaturality
public import Linear.OrderedCrossSpaceCechCoefficientNaturality
public import Linear.NativeIndependentSourceAmbientCechObjects
public import Linear.ConcreteAdditiveEquivNaturality
public import Linear.NativeProjectiveDegreeZeroActualCoefficientValue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option diagnostics true
set_option diagnostics.threshold 1000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M N : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module K N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (hRD : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hSD : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hRE : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (hSE : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
variable [DirectSum.Decomposition D] [DirectSum.Decomposition E]
variable [IsScalarTower K R M] [IsScalarTower K S M]
variable [IsScalarTower K R N] [IsScalarTower K S N]
variable [IsDomain S] [Module.IsTorsionFree S M] [Module.IsTorsionFree S N]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [Module.Finite R M] [Module.Finite S M] [Module.Finite R N] [Module.Finite S N]
variable {ι κ : Type u} (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable (c : κ → S) (hc : ∀ i,c i ∈ B 1)
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv
open CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
variable [LinearOrder ι]
variable [Finite ι] [Algebra.FiniteType K S] [Module.Finite R S]
attribute [local irreducible] finiteTypeNativeProj_orderedActualHigherHIso
  noetherianFiniteOrderedAffineCover_actualHigherHIso topFiniteOrderedCech_actualHigherHIso_of_localAcyclic
  nativeIndependentSourceAmbientOrderedTwistCechIso orderedFreeSheafActualHomComplexIso
  acyclicResolutionActualCochainExtIso
/-- SAME original source/ambient Cech homology iso,with named exact objects. -/
def nativeIndependentFiniteNormalization_cachedCechHomologyIso
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ) :
    nativeProjectiveOrderedCechHomologyObject A D hRD a k (q+1) ≅
      nativeProjectiveOrderedCechHomologyObject B D hSD (fun i => algebraMap R S (a i)) k (q+1) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) (q+1)).mapIso
    (nativeIndependentSourceAmbientOrderedTwistCechIso A B D hRD hSD a ha c hc hgenR hgenC k)
/-- The SAME original all-twist Cech homology coefficient square,with
named objects and original coefficient maps;no new square is assumed. -/
theorem nativeIndependentFiniteNormalization_cachedCechHomologyIso_coefficient
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ) :
    nativeProjectiveOrderedCechHomologyCoefficientHom A D E hRD hRE (f.restrictScalars R) hf a k (q+1) ≫
      (nativeIndependentFiniteNormalization_cachedCechHomologyIso A B E hRE hSE a ha c hc hgenR hgenC k q).hom =
    (nativeIndependentFiniteNormalization_cachedCechHomologyIso A B D hRD hSD a ha c hc hgenR hgenC k q).hom ≫
      nativeProjectiveOrderedCechHomologyCoefficientHom B D E hSD hSE f hf
        (fun i => algebraMap R S (a i)) k (q+1) := by
  exact nativeIndependentSourceAmbientOrderedTwistCechIso_homology_coefficient A B D E hRD hSD hRE hSE f hf
    a ha c hc hgenR hgenC k q
end LinearStudy
