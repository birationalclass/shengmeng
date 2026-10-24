module
public import Linear.NativeIntegerFreeRelationMatrixDuality
public import Linear.NativeShiftedFreePresentationTopCechCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K M : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
variable [IsScalarTower K (MvPolynomial σ K) M]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual ORIGINAL coordinate-Cech top homology of M is the
ACTUAL cokernel of the original relation homology map,for the original
weighted free presentation with EVERY ORIGINAL INTEGER weight. No cokernel/exactness/vanishing premise is
added;these were proved by the general actual Noetherian presentation. -/
def coordinateNativeIntegerPresentationTopCokernelIso {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (z : I → ℤ) (w : J → ℤ)
    (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
    (hD : ∀ t : ℕ, ∀ d : ℤ, ∀ p : MvPolynomial σ K, p ∈ homogeneousSubmodule σ K t →
      ∀ x : M, x ∈ D d → p • x ∈ D ((t:ℤ)+d))
    (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
    (β : (J → MvPolynomial σ K) →ₗ[MvPolynomial σ K] M)
    (hc : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
      x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
        z d →
      c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
        w d)
    (hβ : ∀ d : ℤ, ∀ x : J → MvPolynomial σ K,
      x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
        w d → β x ∈ D d)
    (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)
    (n : ℕ) (hcard : Fintype.card σ=n+2) :
    cokernel ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          z)
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          w)
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          z)
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          w) c hc 0)) ≅
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
      (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD 0) :=
  LinearStudy.nativeShiftedFreePresentationOrderedCech_topCokernelIso (homogeneousSubmodule σ K)
    z
    w D hD c β hc hβ
    (fun i : ULift σ => X i.down) (fun i => isHomogeneous_X K i.down)
    (iSup_coordinateOpenCover_eq_top (R := K) (σ := σ))
    (homogeneousProjπ (R := K) (σ := σ)) honto hex 0 (n+1)
    (by simpa only [Fintype.card_ulift] using hcard)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ)
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hD : ∀ t : ℕ, ∀ d : ℤ, ∀ p : MvPolynomial σ K, p ∈ homogeneousSubmodule σ K t →
  ∀ x : M, x ∈ D d → p • x ∈ D ((t:ℤ)+d))
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (β : (J → MvPolynomial σ K) →ₗ[MvPolynomial σ K] M)
variable (hc : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    z d →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    w d)
variable (hβ : ∀ d : ℤ, ∀ x : J → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    w d → β x ∈ D d)
variable (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)
variable (n : ℕ) (hcard : Fintype.card σ=n+2)

/-- The actual coordinate-presentation Cech comparison preserves the
ORIGINAL quotient map beta on ACTUAL top ordered-Cech homology. -/
theorem coordinateNativeIntegerPresentationTopCokernelIso_quotient :
    cokernel.π ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          z)
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          w)
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          z)
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          w) c hc 0)) ≫
      (coordinateNativeIntegerPresentationTopCokernelIso z w D hD c β hc hβ honto hex n hcard).hom =
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          w) D
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          w) hD β hβ 0) :=
  LinearStudy.nativeShiftedFreePresentationOrderedCech_topCokernelIso_quotient (homogeneousSubmodule σ K)
    z
    w D hD c β hc hβ
    (fun i : ULift σ => X i.down) (fun i => isHomogeneous_X K i.down)
    (iSup_coordinateOpenCover_eq_top (R := K) (σ := σ))
    (homogeneousProjπ (R := K) (σ := σ)) honto hex 0 (n+1)
    (by simpa only [Fintype.card_ulift] using hcard)


end MvPolynomial
