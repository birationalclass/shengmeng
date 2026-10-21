module
public import Linear.NativeIndependentNormalizationModuleHComparison
public import Linear.IntegerPresentationDataCoordinateIndependence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
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
variable [IsDomain S] [Module.IsTorsionFree S M] [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite (MvPolynomial σ K) S] [Module.Finite (MvPolynomial σ K) M] [Module.Finite S M]
/-- Specified additive actual-H/ORIGINAL homogeneous-Hom comparison.
Valid presentation DATA is chosen first;the concrete Cech comparison is
constructed from it,then the SAME actual-H comparison is composed.
No arbitrary whole-Iso choice and no normalized geometric trace claim. -/
def nativeFiniteNormalization_specifiedActualTopHomDualIso
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ) :
    AddCommGrpCat.of (schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1)) ≅
      (forget₂ (ModuleCat K) AddCommGrpCat).obj (ModuleCat.of K (Module.Dual K
        (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ : ℤ)-k)))) := by
  let A := MvPolynomial.homogeneousSubmodule σ K
  let eD := MvPolynomial.coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso D hR q hcard k
  let a : ULift.{0} σ → MvPolynomial σ K := fun i => MvPolynomial.X i.down
  have ha : ∀ i,a i ∈ A 1 := fun i => MvPolynomial.isHomogeneous_X K i.down
  have hgenA : Algebra.adjoin K (Set.range a) = ⊤ := by
    have hrange : Set.range a = Set.range (MvPolynomial.X : σ → MvPolynomial σ K) := by
      ext x
      constructor
      · rintro ⟨i,rfl⟩;exact ⟨i.down,rfl⟩
      · rintro ⟨i,rfl⟩;exact ⟨ULift.up i,rfl⟩
    rw [hrange]
    exact MvPolynomial.adjoin_range_X
  let eH := nativeIndependentFiniteNormalization_moduleCechActualHigherHIso A B D hR hS
    a ha c hc (MvPolynomial.homogeneousProjπ (R:=K) (σ:=σ)) hgenA hgenC k q
  exact eH.symm ≪≫ (forget₂ (ModuleCat K) AddCommGrpCat).mapIso eD
end LinearStudy
