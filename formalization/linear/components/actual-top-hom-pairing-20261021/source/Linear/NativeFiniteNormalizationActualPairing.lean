module
public import Linear.NativeFiniteNormalizationActualTopDuality
public import Linear.ActualAdditiveDualPairing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
attribute [local irreducible] nativeFiniteNormalization_actualTopHomDualIso
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
/-- Actual evaluation pairing derived from SAME native top-H/graded-Hom
comparison. It is additive in H and K-linear in the Hom coefficient. -/
def nativeFiniteNormalizationActualTopPairing
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ) :
    schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1) →+
      Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ : ℤ)-k)) :=
  (nativeFiniteNormalization_actualTopHomDualIso (K := K) (S := S) (M := M) (σ := σ)
    B D hR hS c hc hgenC q hcard k).addCommGroupIsoToAddEquiv.toAddMonoidHom
/-- The pairing evaluates the SAME constructed actual-H comparison. -/
theorem nativeFiniteNormalizationActualTopPairing_apply
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ)
    (h : schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1))
    (phi : integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ : ℤ)-k)) :
    nativeFiniteNormalizationActualTopPairing (K := K) (S := S) (M := M) (σ := σ) B D hR hS c hc hgenC q hcard k h phi =
      (show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D
        (-(Fintype.card σ : ℤ)-k)) from
          (nativeFiniteNormalization_actualTopHomDualIso (K := K) (S := S) (M := M) (σ := σ)
            B D hR hS c hc hgenC q hcard k).hom h) phi := rfl
attribute [local irreducible] nativeFiniteNormalizationActualTopPairing
/-- Actual top-H pairing is left nondegenerate,derived rather than assumed. -/
theorem nativeFiniteNormalizationActualTopPairing_left_nondegenerate
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ)
    (h : schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1))
    (hz : ∀ phi,nativeFiniteNormalizationActualTopPairing (K := K) (S := S) (M := M) (σ := σ) B D hR hS c hc hgenC q hcard k h phi=0) : h=0 := by
  unfold nativeFiniteNormalizationActualTopPairing at hz
  apply additiveDualComparisonPairing_left_nondegenerate (K := K) (H := schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1)) (V := integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ : ℤ)-k)) ((nativeFiniteNormalization_actualTopHomDualIso (K := K) (S := S) (M := M) (σ := σ) B D hR hS c hc hgenC q hcard k).addCommGroupIsoToAddEquiv) h
  simpa only [additiveDualComparisonPairing] using hz
/-- Actual top-H pairing is right nondegenerate,derived using ordinary
field dual separation. This does not identify a normalized geometric trace. -/
theorem nativeFiniteNormalizationActualTopPairing_right_nondegenerate
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) (k : ℤ)
    (phi : integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ : ℤ)-k))
    (hz : ∀ h,nativeFiniteNormalizationActualTopPairing (K := K) (S := S) (M := M) (σ := σ) B D hR hS c hc hgenC q hcard k h phi=0) : phi=0 := by
  unfold nativeFiniteNormalizationActualTopPairing at hz
  apply additiveDualComparisonPairing_right_nondegenerate (K := K) (H := schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B D hS k) (q+1)) (V := integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D (-(Fintype.card σ : ℤ)-k)) ((nativeFiniteNormalization_actualTopHomDualIso (K := K) (S := S) (M := M) (σ := σ) B D hR hS c hc hgenC q hcard k).addCommGroupIsoToAddEquiv) phi
  simpa only [additiveDualComparisonPairing] using hz
end LinearStudy
