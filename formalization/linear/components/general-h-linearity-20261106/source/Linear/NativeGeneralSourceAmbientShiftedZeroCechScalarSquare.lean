module
public import Linear.NativeGeneralSourceAmbientOrderedCech
public import Linear.NativeGeneralSourceAmbientOrderedCechScalar
public import Linear.NativeGeneralSourceAmbientShiftedZeroCechComparison
public import Linear.NativeProjectiveOrderedBaseScalarMap
public import Linear.OrderedCrossSpaceCechEndomorphism
public import Linear.OrderedFreeSheafHomCoefficientNaturality
public import Linear.OrderedCrossSpaceAbelianCechIso
public import Linear.OrderedFreeSheafHomComplex
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
open CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
variable [LinearOrder ι]
attribute [local irreducible] nativeProjectiveModuleSheaf nativeProjectiveModulePresheaf
  schemeModuleToActualAbelianSheaf originalGlobalModuleScalar
  nativeIndependentSourceAmbientCechProductFamily_general nativeIndependentSourceAmbientCechProductIso_general
  orderedCrossSpaceAbelianCechComplexIso orderedFormalCechComplex FormalCoproduct.evalOp
attribute [local irreducible] nativeIndependentSourceAmbientOrderedCechIso_general
  orderedTopAbelianCechCoefficientMap orderedTopAbelianCechCoefficientIso nativeProjectiveTwistRegradingIso
/-- Apply the proved zero-twist original scalar square to the original shifted grading. -/
def nativeIndependentSourceAmbientShiftedZeroCechIso_baseScalar_general_square
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :=
  letI : DirectSum.Decomposition (integerGradingShift D k) := integerGradingShiftDecomposition D k
  show CommSq _ _ _ _ from ⟨(nativeIndependentSourceAmbientOrderedCechIso_baseScalar_general A B
    (integerGradingShift D k)
    (integerGradingShift_smul_homogeneous A D hR k) (integerGradingShift_smul_homogeneous B D hS k)
    a ha c hc hgenR hgenC r).symm⟩
end LinearStudy
