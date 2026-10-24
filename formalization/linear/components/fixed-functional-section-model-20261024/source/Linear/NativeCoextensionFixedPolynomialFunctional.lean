module
public import Linear.NativeCoextensionOriginalRingRepresentative
public import Linear.NativeCoextensionSpecifiedGradedRepresentative
public import Linear.NativeCoextensionSpecifiedTraceAdjointPairing
public import Linear.IntegerGradedHomPieceFinite
public import Linear.FiniteAdditiveDualNonzeroRepresentative
public import Linear.OriginalGradedCoextensionRingGenerator
public import Linear.NativeRingIntegerDecomposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K S : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [CommRing S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
variable [IsScalarTower K (MvPolynomial σ K) S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) B]
variable [IsDomain S] [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite (MvPolynomial σ K) S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  coextensionGradedDecomposition coextensionOriginalBaseScalarTower
attribute [local instance] coextensionTraceBaseSourceTower coextensionTraceFieldSourceTower
  coextensionTraceFiniteBase coextensionTraceFiniteSource coextensionTraceTorsionFree
  schemeModuleActualCohomologyAddCommGroup
attribute [local irreducible] nativeFiniteNormalization_specifiedActualTopHomDualIso
attribute [local instance] nativeProjectiveRingIntegerDecomposition
attribute [local irreducible] nativeProjectiveModuleSheaf
/-- Full fixed-degree functional-to-polynomial proposition. STATEMENT
only;the following theorem proves it from an already constructed actual
graded polynomial lifting rule. The original-V application supplies that
rule,not an unproved desired functional-to-polynomial conclusion. -/
def nativeCoextensionFixedPolynomialFunctionalStatement
    {τ : Type} (P : MvPolynomial τ K →ₐ[K] S) (I : Ideal (MvPolynomial τ K))
    (m : ℕ)
    (e : ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))) →ₗ[S] S)
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) : Prop :=
  let A := MvPolynomial.homogeneousSubmodule σ K
  let D := nativeProjectiveRingIntegerPiece B
  let C := (ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj
    (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))
  let hR := nativeRingIntegerBaseGradeCompatibility A B
  let hS := nativeProjectiveRingIntegerPiece_graded B
  let k : ℤ := -(Fintype.card σ:ℤ)
  let F := nativeProjectiveModuleSheaf B D hS k
  let H := schemeModuleActualCohomology (Proj B) F (q+1)
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let W : Type := integerGradedHomPiece A D (k-k)
  let J := nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard k
  let comparison : H ≃+ Module.Dual K W := actualAbelianIsoAddEquiv (K:=K) (H:=H) (V:=W) J
  ∀ ell : H →+ K,
    (∀ a : K,∀ x : H,ell (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
      (originalGlobalModuleScalar (piB.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) F)) (q+1) x)=a * ell x) →
    ell ≠ 0 →
    ∃ z : C,z ∈ coextensionGradedPiece A B 0 ∧ z ≠ 0 ∧
      ∃ Q : MvPolynomial τ K,Q.IsHomogeneous m ∧ Q ∉ I ∧ P Q=e z ∧
        ∃ psi : W,z=coextensionOriginalAdjoint (S:=S) psi.1 (1:S) ∧ ∀ x : H,
          comparison x psi=ell x
/-- Compose the ACTUAL retained original dual representative with a
fixed already proved polynomial image rule. Original V discharges this
algebraic rule using its constructed uniform graded embedding. -/
theorem nativeCoextensionFixedPolynomialFunctionalStatement_of_images
    {τ : Type} (P : MvPolynomial τ K →ₐ[K] S) (I : Ideal (MvPolynomial τ K))
    (m : ℕ)
    (e : ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))) →ₗ[S] S)
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    (hpolynomial : ∀ z,z ∈ coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B 0 → z ≠ 0 →
      ∃ Q : MvPolynomial τ K,Q.IsHomogeneous m ∧ Q ∉ I ∧ P Q=e z) :
    nativeCoextensionFixedPolynomialFunctionalStatement B P I m e c hc hgenC q hcard := by
  dsimp only [nativeCoextensionFixedPolynomialFunctionalStatement]
  let A := MvPolynomial.homogeneousSubmodule σ K
  let D := nativeProjectiveRingIntegerPiece B
  let C := (ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj
    (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))
  let hR := nativeRingIntegerBaseGradeCompatibility A B
  let hS := nativeProjectiveRingIntegerPiece_graded B
  let k : ℤ := -(Fintype.card σ:ℤ)
  let F := nativeProjectiveModuleSheaf B D hS k
  let H := schemeModuleActualCohomology (Proj B) F (q+1)
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let W : Type := integerGradedHomPiece A D (k-k)
  let J := nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard k
  let comparison : H ≃+ Module.Dual K W := actualAbelianIsoAddEquiv (K:=K) (H:=H) (V:=W) J
  intro ell hlinear hell
  have hrep : ∃ z : C,z ∈ coextensionGradedPiece A B 0 ∧ z ≠ 0 ∧
      ∃ psi : W,z=coextensionOriginalAdjoint (S:=S) psi.1 (1:S) ∧ ∀ x : H,
        comparison x psi=ell x :=
    nativeCoextensionSpecifiedTopDual_ring_exists_nonzero_zero_degree_element
      (K:=K) (S:=S) (σ:=σ) B c hc hgenC q hcard ell hlinear hell
  obtain ⟨z,hz,hzne,psi,hpsi,hvalue⟩ := hrep
  obtain ⟨Q,hQ,hQne,hQval⟩ := hpolynomial z hz hzne
  exact ⟨z,hz,hzne,Q,hQ,hQne,hQval,psi,hpsi,hvalue⟩
end LinearStudy
