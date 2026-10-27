module
public import Linear.SpecifiedDualityFactorizationData
public import Linear.NativeGeneralSpecifiedNormalizationAbelianFactorization
public import Linear.IntegerFinitePresentationAbelianComparisonFactorization
public import Linear.IntegerPresentationDataCoordinateIndependence
/- Arbitrary finite coefficients;the original fraction maps,ordered signs and actual-H objects are retained.Normalized dualizing trace remains OPEN. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K S M : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [CommRing S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
variable [IsScalarTower K (MvPolynomial σ K) S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) B]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M] [Module S M]
variable [IsScalarTower (MvPolynomial σ K) S M] [IsScalarTower K (MvPolynomial σ K) M] [IsScalarTower K S M]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ d : ℕ,∀ j : ℤ,∀ z : MvPolynomial σ K,z ∈ MvPolynomial.homogeneousSubmodule σ K d →
  ∀ x : M,x ∈ D j → z • x ∈ D ((d : ℤ)+j))
variable (hS : ∀ d : ℕ,∀ j : ℤ,∀ z : S,z ∈ B d → ∀ x : M,x ∈ D j → z • x ∈ D ((d : ℤ)+j))
variable [IsDomain S] [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite (MvPolynomial σ K) S] [Module.Finite (MvPolynomial σ K) M] [Module.Finite S M]
attribute [local irreducible] nativeProjectiveModuleSheaf schemeModuleToActualAbelianSheaf
  nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general
/-- Actual ORIGINAL comparison data,constructed from the proved constituent
maps and their exact factorization.No new Iso choice and no desired naturality
square is an input.This is data,not a theorem. -/
def nativeFiniteNormalization_specifiedTopHomFactorizationData_general
    (hgenA : Algebra.adjoin K (Set.range (fun i : ULift.{0} σ => MvPolynomial.X (R:=K) i.down)) = ⊤)
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ) :=
  let A := MvPolynomial.homogeneousSubmodule σ K
  let a : ULift.{0} σ → MvPolynomial σ K := fun i => MvPolynomial.X i.down
  let ha : ∀ i,a i ∈ A 1 := fun i => MvPolynomial.isHomogeneous_X K i.down
  let e := nativeIndependentFiniteNormalization_moduleCechActualHigherHIso_general A B D hR hS a ha c hc
    (MvPolynomial.homogeneousProjπ (R:=K) (σ:=σ)) hgenA hgenC k q
  let j := MvPolynomial.coordinateNativeFiniteIntegerPresentationDataGradedHomDualAbelianIso D hR q hcard k
  originalSpecifiedDualityFactorizationData e j
    (nativeFiniteNormalization_specifiedActualTopHomDualIso_general B D hR hS c hc hgenC q hcard k)
    (nativeFiniteNormalization_specifiedActualTopHomDualIso_abelian_factorization_general B D hR hS hgenA
      c hc hgenC q hcard k)
end LinearStudy
