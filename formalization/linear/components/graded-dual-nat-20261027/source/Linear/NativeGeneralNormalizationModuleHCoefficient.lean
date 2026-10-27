module
public import Linear.NativeGeneralNormalizationActualHCoefficient
public import Linear.NativeGeneralNormalizationModuleHFactorization
public import Linear.CategoricalComparisonCoefficientFactorization
public import Linear.NativeGeneralNormalizationModuleHComparison
public import Linear.NativeIndependentNormalizationHFactorization
public import Linear.OrderedModuleCechActualAbelianHomology
public import Linear.NativeIndependentNormalizationActualHFactorization
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
attribute [local irreducible] nativeProjectiveOrderedModuleCechHomologyIso
  nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general
  nativeWeightedSourceAmbientSectionAddEquiv
  nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf schemeModuleToActualAbelianSheaf
  nativeIndependentFiniteNormalization_actualHigherHIso_general
  orderedModuleCechActualAbelianHomologyIso orderedModuleCechActualAbelianComplexIso
  AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex orderedBaseCechActualCoefficientMap
  schemeModuleActualHObject schemeModuleActualHCoefficientHom
  HomologicalComplex.homologyFunctor
open CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
variable [LinearOrder ι]
attribute [local irreducible] orderedFormalCechComplex FormalCoproduct.evalOp orderedTopAbelianCechComplex
  orderedTopAbelianCechCoefficientMap
variable [Finite ι] [Algebra.FiniteType K S] [Module.Finite R S]
attribute [local irreducible] finiteTypeNativeProj_orderedActualHigherHIso
  noetherianFiniteOrderedAffineCover_actualHigherHIso topFiniteOrderedCech_actualHigherHIso_of_localAcyclic
  nativeIndependentSourceAmbientOrderedTwistCechIso orderedFreeSheafActualHomComplexIso
  acyclicResolutionActualCochainExtIso
/-- The SAME original module-valued ambient-Cech/source-H comparison is
natural for the ORIGINAL degree-zero map,EVERY integer twist and positive
degree. Original module-homology forgetting and actual coefficient maps
are retained;no comparison square is supplied as a hypothesis. -/
theorem nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_coefficient_general
    {Y : Scheme.{u}} (pi : Proj A ⟶ Y)
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) (q : ℕ) :
    nativeProjectiveOrderedModuleCechHomologyCoefficientHom A D E hRD hRE pi
      (f.restrictScalars R) hf a k (q+1) ≫
      (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general A B E hRE hSE a ha c hc pi hgenR hgenC k q).hom =
    (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general A B D hRD hSD a ha c hc pi hgenR hgenC k q).hom ≫
      schemeModuleActualHCoefficientHom (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf k) (q+1) := by
  let eM := nativeProjectiveOrderedModuleCechHomologyIso A D hRD pi a k (q+1)
  let eN := nativeProjectiveOrderedModuleCechHomologyIso A E hRE pi a k (q+1)
  let jM := nativeIndependentFiniteNormalization_actualHigherHIso_general A B D hRD hSD a ha c hc hgenR hgenC k q
  let jN := nativeIndependentFiniteNormalization_actualHigherHIso_general A B E hRE hSE a ha c hc hgenR hgenC k q
  exact originalComparisonIsoCoefficientSquare_of_factorizations eM eN jM jN
    (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general A B D hRD hSD a ha c hc pi hgenR hgenC k q)
    (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general A B E hRE hSE a ha c hc pi hgenR hgenC k q)
    (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_factorization_general A B D hRD hSD a ha c hc pi hgenR hgenC k q)
    (nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_factorization_general A B E hRE hSE a ha c hc pi hgenR hgenC k q)
    (nativeProjectiveOrderedModuleCechHomologyCoefficientHom A D E hRD hRE pi (f.restrictScalars R) hf a k (q+1))
    (nativeProjectiveOrderedCechHomologyCoefficientHom A D E hRD hRE (f.restrictScalars R) hf a k (q+1))
    (schemeModuleActualHCoefficientHom (nativeProjectiveDegreeZeroSheafMap B D E hSD hSE f hf k) (q+1))
    (nativeProjectiveOrderedModuleCechHomologyIso_coefficient A D E hRD hRE pi (f.restrictScalars R) hf a k (q+1))
    (nativeIndependentFiniteNormalization_actualHigherHIso_coefficient_general A B D E hRD hSD hRE hSE f hf
      a ha c hc hgenR hgenC k q)
end LinearStudy
