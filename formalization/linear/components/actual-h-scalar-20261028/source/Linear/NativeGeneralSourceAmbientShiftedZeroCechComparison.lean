module
public import Linear.NativeGeneralSourceAmbientOrderedCech
public import Linear.NativeProjectiveTwistRegrading
public import Linear.NativeFiniteGradedSourceAmbientOrderedTwistCech
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
  schemeModuleToActualAbelianSheaf nativeIndependentSourceAmbientOrderedCechIso_general
  orderedFormalCechComplex FormalCoproduct.evalOp
/-- The SAME original zero-twist comparison of shifted graded modules,with exact original Cech objects cached. -/
def nativeIndependentSourceAmbientShiftedZeroCechIso_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) :
    orderedTopAbelianCechComplex (Proj A) (fun i => Proj.basicOpen A (a i))
      ((schemeModuleToActualAbelianSheaf (Proj A)).obj (nativeProjectiveModuleSheaf A (integerGradingShift D k)
        (integerGradingShift_smul_homogeneous A D hR k) 0)) ≅
    orderedTopAbelianCechComplex (Proj B) (fun i => Proj.basicOpen B (algebraMap R S (a i)))
      ((schemeModuleToActualAbelianSheaf (Proj B)).obj (nativeProjectiveModuleSheaf B (integerGradingShift D k)
        (integerGradingShift_smul_homogeneous B D hS k) 0)) := by
  letI : DirectSum.Decomposition (integerGradingShift D k) := integerGradingShiftDecomposition D k
  exact nativeIndependentSourceAmbientOrderedCechIso_general A B (integerGradingShift D k)
    (integerGradingShift_smul_homogeneous A D hR k) (integerGradingShift_smul_homogeneous B D hS k)
    a ha c hc hgenR hgenC
end LinearStudy
