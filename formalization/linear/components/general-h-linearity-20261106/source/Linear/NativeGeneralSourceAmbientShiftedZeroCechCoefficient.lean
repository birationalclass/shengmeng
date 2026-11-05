module
public import Linear.NativeGeneralSourceAmbientOrderedCechCoefficientTyped
public import Linear.NativeGeneralSourceAmbientOrderedTwistCech
public import Linear.NativeProjectiveCechCoefficientObjects
public import Linear.NativeGeneralSourceAmbientShiftedZeroCechComparison
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
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 5000
set_option diagnostics true
set_option diagnostics.threshold 100
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
  nativeIndependentSourceAmbientOrderedCechIso_general nativeIndependentSourceAmbientOrderedTwistCechIso_general
open CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
variable [LinearOrder ι]
attribute [local irreducible] orderedFormalCechComplex FormalCoproduct.evalOp
  nativeProjectiveTwistRegradingIso orderedTopAbelianCechCoefficientIso
  orderedTopAbelianCechCoefficientMap
/-- Original shifted zero-twist naturality; no torsion-free coefficient premise. -/
theorem nativeIndependentSourceAmbientShiftedZeroCechIso_coefficient_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) :
    let Dk := integerGradingShift D k
    let Ek := integerGradingShift E k
    let hRDk := integerGradingShift_smul_homogeneous A D hRD k
    let hSDk := integerGradingShift_smul_homogeneous B D hSD k
    let hREk := integerGradingShift_smul_homogeneous A E hRE k
    let hSEk := integerGradingShift_smul_homogeneous B E hSE k
    let hfk := fun j x hx => hf (j+k) x hx
    CommSq
      (nativeProjectiveOrderedCechCoefficientMap A Dk Ek hRDk hREk (f.restrictScalars R) hfk
        (fun i => Proj.basicOpen A (a i)) 0)
      (nativeIndependentSourceAmbientShiftedZeroCechIso_general A B D hRD hSD a ha c hc hgenR hgenC k).hom
      (nativeIndependentSourceAmbientShiftedZeroCechIso_general A B E hRE hSE a ha c hc hgenR hgenC k).hom
      (nativeProjectiveOrderedCechCoefficientMap B Dk Ek hSDk hSEk f hfk
        (fun i => Proj.basicOpen B (algebraMap R S (a i))) 0) := by
  dsimp only
  letI : DirectSum.Decomposition (integerGradingShift D k) := integerGradingShiftDecomposition D k
  letI : DirectSum.Decomposition (integerGradingShift E k) := integerGradingShiftDecomposition E k
  exact ⟨(nativeIndependentSourceAmbientOrderedCechIso_coefficient_general_typed A B
    (integerGradingShift D k) (integerGradingShift E k)
    (integerGradingShift_smul_homogeneous A D hRD k) (integerGradingShift_smul_homogeneous B D hSD k)
    (integerGradingShift_smul_homogeneous A E hRE k) (integerGradingShift_smul_homogeneous B E hSE k)
    f (fun j x hx => hf (j+k) x hx) a ha c hc hgenR hgenC).symm⟩
end LinearStudy
