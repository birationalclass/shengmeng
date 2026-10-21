module
public import Linear.NativeIndependentNormalizationModuleHLinearComparison
public import Linear.SchemeModuleActualHSpecScalars
public import Linear.NativeSpecifiedNormalizationActualTopDuality
public import Linear.CoordinateNativeCechHomologyModel
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
/-- The ORIGINAL normalization comparison restricted through GammaSpecIso,
as an actual isomorphism in ModuleCat K. Keep bundled module objects;
its complete result type is exported by the exact declaration audit. -/
def nativeFiniteNormalization_moduleCechActualHigherHKLinearIso
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (q : ℕ) (k : ℤ) :=
  let A := MvPolynomial.homogeneousSubmodule σ K
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  letI := schemeModuleActualHBaseModule piB (nativeProjectiveModuleSheaf B D hS k) (q+1)
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
  let e := nativeIndependentFiniteNormalization_moduleCechActualHigherHLinearEquiv
    A B D hR hS a ha c hc hgenA hgenC k q
  let j := MvPolynomial.coordinateNativeCechHomologyFunctorModelIso q
    (nativeProjectiveModuleSheaf A D hR k)
  let F := ModuleCat.restrictScalars (MvPolynomial.coordinateCanonicalCoefficientRingEquiv K).toRingHom
  F.mapIso (j ≪≫ e.toModuleIso)
end LinearStudy
