module
public import Linear.NativeGeneralSourceAmbientShiftedZeroCechComparison
public import Linear.NativeGeneralSourceAmbientOrderedTwistCech
public import Linear.NativeProjectiveCechCoefficientObjects
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
/-- Exact factorization of the SAME public twist comparison into the
original regrading isos and the original shifted zero-twist comparison. -/
theorem nativeIndependentSourceAmbientOrderedTwistCechIso_factorization_general
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ) :
    nativeIndependentSourceAmbientOrderedTwistCechIso_general A B D hR hS a ha c hc hgenR hgenC k =
      (nativeProjectiveOrderedCechRegradingIso A D hR (fun i => Proj.basicOpen A (a i)) k).symm ≪≫
      nativeIndependentSourceAmbientShiftedZeroCechIso_general A B D hR hS a ha c hc hgenR hgenC k ≪≫
      nativeProjectiveOrderedCechRegradingIso B D hS (fun i => Proj.basicOpen B (algebraMap R S (a i))) k := rfl
end LinearStudy
