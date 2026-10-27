module
public import Linear.IntegerFinitePresentationAbelianComparisonCoefficientProof
public import Linear.IntegerGradedHomDualCoefficientObjects
public import Linear.SpecifiedDualityCoefficientTransfer
public import Linear.NativeGeneralSpecifiedNormalizationTopDuality
public import Linear.NativeGeneralSpecifiedNormalizationCoefficientData
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
/-- The ORIGINAL module-Cech/actual-H coefficient square specialized to the
standard polynomial normalization,including torsion source and target. -/
def nativePolynomialFiniteNormalizationModuleHCoefficient_general
    (hgenA : Algebra.adjoin K (Set.range (fun i : ULift.{0} σ => MvPolynomial.X (R:=K) i.down)) = ⊤)
    (f : M →ₗ[S] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (q : ℕ) (k : ℤ) :=
  nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_coefficient_general
    (MvPolynomial.homogeneousSubmodule σ K) B D E hRM hSM hRN hSN f hf
    (fun i : ULift.{0} σ => MvPolynomial.X i.down)
    (fun i => MvPolynomial.isHomogeneous_X K i.down) c hc
    (MvPolynomial.homogeneousProjπ (R:=K) (σ:=σ)) hgenA hgenC k q
end LinearStudy
