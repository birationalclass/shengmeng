module
public import Linear.IntegerFinitePresentationAbelianComparisonCoefficientProof
public import Linear.IntegerGradedHomDualCoefficientObjects
public import Linear.SpecifiedDualityCoefficientTransfer
public import Linear.NativeGeneralSpecifiedNormalizationTopDuality
public import Linear.NativeGeneralSpecifiedNormalizationTopDualityCoefficient
public import Linear.NativeGeneralSpecifiedNormalizationCoefficientDataIdentity
public import Linear.NativeGeneralNormalizationModuleHCoefficient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
set_option diagnostics true
set_option diagnostics.threshold 100
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K S M N : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [CommRing S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
variable [IsScalarTower K (MvPolynomial σ K) S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) B]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M] [Module S M]
variable [IsScalarTower (MvPolynomial σ K) S M] [IsScalarTower K (MvPolynomial σ K) M] [IsScalarTower K S M]
variable [AddCommGroup N] [Module K N] [Module (MvPolynomial σ K) N] [Module S N]
variable [IsScalarTower (MvPolynomial σ K) S N] [IsScalarTower K (MvPolynomial σ K) N] [IsScalarTower K S N]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (E : ℤ → Submodule K N) [DirectSum.Decomposition E]
variable (hRM : ∀ t : ℕ,∀ j : ℤ,∀ z : MvPolynomial σ K,z ∈ MvPolynomial.homogeneousSubmodule σ K t → ∀ x : M,x ∈ D j → z • x ∈ D ((t:ℤ)+j))
variable (hSM : ∀ t : ℕ,∀ j : ℤ,∀ z : S,z ∈ B t → ∀ x : M,x ∈ D j → z • x ∈ D ((t:ℤ)+j))
variable (hRN : ∀ t : ℕ,∀ j : ℤ,∀ z : MvPolynomial σ K,z ∈ MvPolynomial.homogeneousSubmodule σ K t → ∀ x : N,x ∈ E j → z • x ∈ E ((t:ℤ)+j))
variable (hSN : ∀ t : ℕ,∀ j : ℤ,∀ z : S,z ∈ B t → ∀ x : N,x ∈ E j → z • x ∈ E ((t:ℤ)+j))
variable [IsDomain S]
variable [IsNoetherianRing S] [Algebra.FiniteType K S] [Module.Finite (MvPolynomial σ K) S]
variable [Module.Finite (MvPolynomial σ K) M] [Module.Finite S M]
variable [Module.Finite (MvPolynomial σ K) N] [Module.Finite S N]
attribute [local irreducible] AlgebraicGeometry.Spec MvPolynomial.homogeneousProjπ
  nativeProjectiveModuleSheaf schemeModuleToActualAbelianSheaf
  nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general
  nativeFiniteNormalization_specifiedActualTopHomDualIso_general schemeModuleActualHObject
  schemeModuleActualHCoefficientHom integerGradedHomPiece
  MvPolynomial.coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso
  MvPolynomial.coordinateNativeFiniteIntegerPresentationDataGradedHomDualAbelianIso
/-- COMPLETE naturality for the SAME publicly specified comparison and the
ORIGINAL coefficient maps,including torsion source and target. Every retained
condition is geometric or algebraic;no desired comparison square is assumed. -/
theorem nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficient_general_typed
    (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ) :
    schemeModuleActualHCoefficientHom (nativeProjectiveDegreeZeroSheafMap B D E hSM hSN f hf k) (q+1) ≫
      (nativeFiniteNormalization_specifiedActualTopHomDualIso_general B E hRN hSN c hc hgenC q hcard k).hom =
    (nativeFiniteNormalization_specifiedActualTopHomDualIso_general B D hRM hSM c hc hgenC q hcard k).hom ≫
      integerGradedHomDualCoefficientHom (MvPolynomial.homogeneousSubmodule σ K) D E
        (f.restrictScalars (MvPolynomial σ K)) hf (-(Fintype.card σ:ℤ)-k) := by
  simpa only [nativeFiniteNormalization_specifiedTopHomFactorizationData_specified_general] using
    (nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficient_general
      B D E hRM hSM hRN hSN f hf c hc hgenC q hcard k)
end LinearStudy
