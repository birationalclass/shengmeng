module
public import Linear.NativeGeneralSourceAmbientOrderedCech
public import Linear.NativeGeneralSourceAmbientShiftedZeroCechScalarSquare
public import Linear.NativeOrderedCechRegradingScalarSquares
public import Linear.NativeGeneralSourceAmbientTwistComparisonFactorization
public import Linear.OriginalThreeIsoScalarSquare
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
attribute [local irreducible] nativeIndependentSourceAmbientShiftedZeroCechIso_general
  nativeProjectiveOrderedCechRegradingIso
/-- Compose the three proved ORIGINAL scalar squares,without assuming
linearity of the whole comparison or transferring an action across it. -/
def nativeIndependentSourceAmbientOrderedTwistCechIso_baseScalar_general_iso_proof
    (hgenR : Algebra.adjoin K (Set.range a) = ⊤)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (k : ℤ)
    (r : Γ(Spec (CommRingCat.of K),⊤)) :=
  let Dk := integerGradingShift D k
  let hRk := integerGradingShift_smul_homogeneous A D hR k
  let hSk := integerGradingShift_smul_homogeneous B D hS k
  letI : DirectSum.Decomposition Dk := integerGradingShiftDecomposition D k
  let U := fun i => Proj.basicOpen A (a i)
  let V := fun i => Proj.basicOpen B (algebraMap R S (a i))
  let eA := orderedTopAbelianCechCoefficientIso U
    ((schemeModuleToActualAbelianSheaf (Proj A)).mapIso (nativeProjectiveTwistRegradingIso A D hR k))
  let eB := orderedTopAbelianCechCoefficientIso V
    ((schemeModuleToActualAbelianSheaf (Proj B)).mapIso (nativeProjectiveTwistRegradingIso B D hS k))
  let e := nativeIndependentSourceAmbientOrderedCechIso_general A B Dk hRk hSk a ha c hc hgenR hgenC
  let hA := nativeProjectiveOrderedCechRegrading_baseScalar_inv_square A D hR
    (fun i => Proj.basicOpen A (a i)) k r
  let hB := nativeProjectiveOrderedCechRegrading_baseScalar_hom_square B D hS
    (fun i => Proj.basicOpen B (algebraMap R S (a i))) k r
  let h0 := nativeIndependentSourceAmbientShiftedZeroCechIso_baseScalar_general_square A B D hR hS a ha c hc
    hgenR hgenC k r
  originalThreeIso_endomorphism_square eA e eB _ _ _ _ hA h0 hB
end LinearStudy
