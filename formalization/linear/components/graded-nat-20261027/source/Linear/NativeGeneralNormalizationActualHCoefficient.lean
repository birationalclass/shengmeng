module
public import Linear.NativeGeneralSourceAmbientOrderedTwistCechCoefficient
public import Linear.NativeIndependentNormalizationActualHFactorization
public import Linear.CategoricalComparisonCoefficientFactorization
public import Linear.NativeGeneralNormalizationActualHFactorization
public import Linear.NativeGeneralNormalizationCachedCechComparison
public import Linear.NativeProjectiveCechHomologyObjects
public import Linear.NativeGeneralSourceAmbientCechHomologyCoefficient
public import Linear.NativeFiniteGradedSourceActualHCoefficient
public import Linear.NativeProjActualHCoefficientNaturality
public import Linear.NativeProjectiveTwistQuasicoherent
public import Linear.FiniteNormalizationCoordinateCover
public import Linear.NativeProjActualHComparison
public import Linear.NativeProjectiveTwistFinitePresentation
public import Linear.NativeGeneralSourceAmbientOrderedTwistCech
public import Linear.NativeOrderedCechRegradingCoefficient
public import Linear.NativeGeneralSourceAmbientOrderedCech
public import Linear.OrderedFreeSheafHomCoefficientNaturality
public import Linear.OrderedCrossSpaceCechCoefficientNaturality
public import Linear.NativeGeneralSourceAmbientCechObjects
public import Linear.ConcreteAdditiveEquivNaturality
public import Linear.NativeProjectiveDegreeZeroActualCoefficientValue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
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
variable [IsDomain R] [IsDomain S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [Module.Finite R M] [Module.Finite S M] [Module.Finite R N] [Module.Finite S N]
variable {ι κ : Type u} (a : ι → R) (ha : ∀ i,a i ∈ A 1)
variable (c : κ → S) (hc : ∀ i,c i ∈ B 1)
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv
  nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf schemeModuleToActualAbelianSheaf
  nativeIndependentSourceAmbientOrderedTwistCechIso_general
  nativeIndependentFiniteNormalization_actualHigherHIso_general
  nativeIndependentFiniteNormalization_cachedCechHomologyIso_general
  nativeProjectiveOrderedCechHomologyObject schemeModuleActualHObject
  nativeProjectiveOrderedCechHomologyCoefficientHom schemeModuleActualHCoefficientHom
  nativeFiniteGradedTwist_cachedActualHigherHIso
open CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
variable [LinearOrder ι]
variable [Finite ι] [Algebra.FiniteType K S] [Module.Finite R S]
attribute [local irreducible] finiteTypeNativeProj_orderedActualHigherHIso
  noetherianFiniteOrderedAffineCover_actualHigherHIso topFiniteOrderedCech_actualHigherHIso_of_localAcyclic
  nativeIndependentSourceAmbientOrderedTwistCechIso orderedFreeSheafActualHomComplexIso
  acyclicResolutionActualCochainExtIso
/-- Naturality of the SAME original finite-normalization actual-H
comparison for EVERY original degree-zero S-linear map,ALL integer twists
and ALL positive degrees. Named objects/maps are EXACT original objects
and maps by proved identities;the comparison equals the OLD specified iso.
No desired coefficient square or global-duality certificate is an input. -/
theorem nativeIndependentFiniteNormalization_actualHigherHIso_coefficient_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ) :
    nativeProjectiveOrderedCechHomologyCoefficientHom A D E hRD hRE (f.restrictScalars R) hf a k (q+1) ≫
      (nativeIndependentFiniteNormalization_actualHigherHIso_general A B E hRE hSE a ha c hc hgenR hgenC k q).hom =
    (nativeIndependentFiniteNormalization_actualHigherHIso_general A B D hRD hSD a ha c hc hgenR hgenC k q).hom ≫
      schemeModuleActualHCoefficientHom (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf k) (q+1) := by
  let eM := nativeIndependentFiniteNormalization_cachedCechHomologyIso_general A B D hRD hSD a ha c hc hgenR hgenC k q
  let eN := nativeIndependentFiniteNormalization_cachedCechHomologyIso_general A B E hRE hSE a ha c hc hgenR hgenC k q
  let jM := nativeFiniteGradedTwist_cachedActualHigherHIso B D hSD
    (fun i => algebraMap R S (a i))
    (fun i => (normalizationBaseGradedRingHom A B).map_mem (ha i))
    (nativeFiniteNormalization_sourceCoordinateCover A B a ha hgenR) k q
  let jN := nativeFiniteGradedTwist_cachedActualHigherHIso B E hSE
    (fun i => algebraMap R S (a i))
    (fun i => (normalizationBaseGradedRingHom A B).map_mem (ha i))
    (nativeFiniteNormalization_sourceCoordinateCover A B a ha hgenR) k q
  exact originalComparisonIsoCoefficientSquare_of_factorizations eM eN jM jN
    (nativeIndependentFiniteNormalization_actualHigherHIso_general A B D hRD hSD a ha c hc hgenR hgenC k q)
    (nativeIndependentFiniteNormalization_actualHigherHIso_general A B E hRE hSE a ha c hc hgenR hgenC k q)
    (nativeIndependentFiniteNormalization_actualHigherHIso_factorization_general A B D hRD hSD a ha c hc hgenR hgenC k q)
    (nativeIndependentFiniteNormalization_actualHigherHIso_factorization_general A B E hRE hSE a ha c hc hgenR hgenC k q)
    (nativeProjectiveOrderedCechHomologyCoefficientHom A D E hRD hRE (f.restrictScalars R) hf a k (q+1))
    (nativeProjectiveOrderedCechHomologyCoefficientHom B D E hSD hSE f hf (fun i => algebraMap R S (a i)) k (q+1))
    (schemeModuleActualHCoefficientHom (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf k) (q+1))
    (nativeIndependentFiniteNormalization_cachedCechHomologyIso_coefficient_general A B D E hRD hSD hRE hSE f hf
      a ha c hc hgenR hgenC k q)
    (nativeFiniteGradedTwist_cachedActualHigherHIso_coefficient B D E hSD hSE f hf
      (fun i => algebraMap R S (a i))
      (fun i => (normalizationBaseGradedRingHom A B).map_mem (ha i))
      (nativeFiniteNormalization_sourceCoordinateCover A B a ha hgenR) k q)
end LinearStudy
