module
public import Linear.NativeCoextensionFixedPolynomialFunctional
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
/-- Exposed per-functional result:the SAME original graded representative,
adjoint-at1 element,and ORIGINAL fixed-degree polynomial with exact image
and comparison values. STATEMENT only,not a theorem. -/
def nativeCoextensionFixedPolynomialRepresentativeStatement
    {τ : Type} (P : MvPolynomial τ K →ₐ[K] S) (I : Ideal (MvPolynomial τ K))
    (m : ℕ)
    (e : ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))) →ₗ[S] S)
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    (ell : schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
        (nativeProjectiveRingIntegerPiece_graded B) (-(Fintype.card σ:ℤ))) (q+1) →+ K) : Prop :=
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
  ∃ z : C,z ∈ coextensionGradedPiece A B 0 ∧ z ≠ 0 ∧
    ∃ Q : MvPolynomial τ K,Q.IsHomogeneous m ∧ Q ∉ I ∧ P Q=e z ∧
      ∃ psi : W,z=coextensionOriginalAdjoint (S:=S) psi.1 (1:S) ∧ ∀ x : H,
        comparison x psi=ell x
/-- Preserve the complete polynomial witness from the previously proved
ALL-functional theorem,without unfolding it inside the chain/section
relation proof. No new polynomial or representative input is added. -/
theorem nativeCoextensionFixedPolynomialRepresentativeStatement_of_functional
    {τ : Type} (P : MvPolynomial τ K →ₐ[K] S) (I : Ideal (MvPolynomial τ K))
    (m : ℕ)
    (e : ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))) →ₗ[S] S)
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    (ell : schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
        (nativeProjectiveRingIntegerPiece_graded B) (-(Fintype.card σ:ℤ))) (q+1) →+ K)
    (hlinear : ∀ a : K,∀ x,
      ell (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
        (originalGlobalModuleScalar
          ((Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))).appTop
            ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))
          (nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
            (nativeProjectiveRingIntegerPiece_graded B) (-(Fintype.card σ:ℤ))))) (q+1) x)=a * ell x)
    (hell : ell ≠ 0)
    (hpoly : nativeCoextensionFixedPolynomialFunctionalStatement B P I m e c hc hgenC q hcard) :
    nativeCoextensionFixedPolynomialRepresentativeStatement B P I m e c hc hgenC q hcard ell := by
  unfold nativeCoextensionFixedPolynomialRepresentativeStatement
  unfold nativeCoextensionFixedPolynomialFunctionalStatement at hpoly
  exact hpoly ell hlinear hell
end LinearStudy
