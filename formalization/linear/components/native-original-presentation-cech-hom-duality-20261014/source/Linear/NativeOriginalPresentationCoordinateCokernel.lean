module
public import Linear.NativeOriginalFreeTopDuality
public import Linear.NativeShiftedFreePresentationTopCechCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K M : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
variable [IsScalarTower K (MvPolynomial σ K) M]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual ORIGINAL coordinate-Cech top homology of M is the
ACTUAL cokernel of the original relation homology map,for the original
weighted free presentation. No cokernel/exactness/vanishing premise is
added;these were proved by the general actual Noetherian presentation. -/
def coordinateNativeOriginalPresentationTopCokernelIso {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (a : I → ℕ) (b : J → ℕ)
    (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
    (hD : ∀ t : ℕ, ∀ d : ℤ, ∀ p : MvPolynomial σ K, p ∈ homogeneousSubmodule σ K t →
      ∀ x : M, x ∈ D d → p • x ∈ D ((t:ℤ)+d))
    (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
    (β : (J → MvPolynomial σ K) →ₗ[MvPolynomial σ K] M)
    (hc : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
      x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
        (fun i => coordinatePresentationWeight (σ := σ) (a i)) d →
      c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
        (fun j => coordinatePresentationWeight (σ := σ) (b j)) d)
    (hβ : ∀ d : ℤ, ∀ x : J → MvPolynomial σ K,
      x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
        (fun j => coordinatePresentationWeight (σ := σ) (b j)) d → β x ∈ D d)
    (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)
    (n : ℕ) (hcard : Fintype.card σ=n+2) :
    cokernel ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          (fun i => coordinatePresentationWeight (σ := σ) (a i)))
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          (fun j => coordinatePresentationWeight (σ := σ) (b j)))
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          (fun i => coordinatePresentationWeight (σ := σ) (a i)))
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          (fun j => coordinatePresentationWeight (σ := σ) (b j))) c hc 0)) ≅
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
      (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD 0) :=
  LinearStudy.nativeShiftedFreePresentationOrderedCech_topCokernelIso (homogeneousSubmodule σ K)
    (fun i => coordinatePresentationWeight (σ := σ) (a i))
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) D hD c β hc hβ
    (fun i : ULift σ => X i.down) (fun i => isHomogeneous_X K i.down)
    (iSup_coordinateOpenCover_eq_top (R := K) (σ := σ))
    (homogeneousProjπ (R := K) (σ := σ)) honto hex 0 (n+1)
    (by simpa only [Fintype.card_ulift] using hcard)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (a : I → ℕ) (b : J → ℕ)
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hD : ∀ t : ℕ, ∀ d : ℤ, ∀ p : MvPolynomial σ K, p ∈ homogeneousSubmodule σ K t →
  ∀ x : M, x ∈ D d → p • x ∈ D ((t:ℤ)+d))
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (β : (J → MvPolynomial σ K) →ₗ[MvPolynomial σ K] M)
variable (hc : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun i => coordinatePresentationWeight (σ := σ) (a i)) d →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) d)
variable (hβ : ∀ d : ℤ, ∀ x : J → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) d → β x ∈ D d)
variable (honto : Function.Surjective β) (hex : LinearMap.range c = LinearMap.ker β)
variable (n : ℕ) (hcard : Fintype.card σ=n+2)

/-- The actual coordinate-presentation Cech comparison preserves the
ORIGINAL quotient map beta on ACTUAL top ordered-Cech homology. -/
theorem coordinateNativeOriginalPresentationTopCokernelIso_quotient :
    cokernel.π ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          (fun i => coordinatePresentationWeight (σ := σ) (a i)))
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          (fun j => coordinatePresentationWeight (σ := σ) (b j)))
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          (fun i => coordinatePresentationWeight (σ := σ) (a i)))
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          (fun j => coordinatePresentationWeight (σ := σ) (b j))) c hc 0)) ≫
      (coordinateNativeOriginalPresentationTopCokernelIso a b D hD c β hc hβ honto hex n hcard).hom =
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          (fun j => coordinatePresentationWeight (σ := σ) (b j))) D
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          (fun j => coordinatePresentationWeight (σ := σ) (b j))) hD β hβ 0) :=
  LinearStudy.nativeShiftedFreePresentationOrderedCech_topCokernelIso_quotient (homogeneousSubmodule σ K)
    (fun i => coordinatePresentationWeight (σ := σ) (a i))
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) D hD c β hc hβ
    (fun i : ULift σ => X i.down) (fun i => isHomogeneous_X K i.down)
    (iSup_coordinateOpenCover_eq_top (R := K) (σ := σ))
    (homogeneousProjπ (R := K) (σ := σ)) honto hex 0 (n+1)
    (by simpa only [Fintype.card_ulift] using hcard)

/-- ACTUAL original coordinate-Cech top homology of M is the ACTUAL
cokernel of the verified canonical polynomial transpose matrix with
entries extracted from original c. The geometric presentation,original
free homology comparison and cokernel matrix square are all constructed. -/
def coordinateNativeOriginalPresentationPolynomialTopCokernelIso :
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
      (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD 0) ≅
    cokernel (coordinateCanonicalGradedPolynomialDualMatrix a b (coordinatePresentationPolynomialEntry a b c hc)) :=
  (coordinateNativeOriginalPresentationTopCokernelIso a b D hD c β hc hβ honto hex n hcard).symm.trans
    (cokernel.mapIso _ _ (coordinateNativeOriginalFreeTopHomologyDualIso a n hcard)
      (coordinateNativeOriginalFreeTopHomologyDualIso b n hcard)
      (coordinateNativeOriginalFreeRelation_top_duality a b c hc n hcard))

/-- The actual original quotient on coordinate-Cech top homology is
compatible with the original canonical polynomial matrix quotient,
not just an abstract isomorphism of vector spaces. -/
theorem coordinateNativeOriginalPresentationPolynomialTopCokernelIso_quotient :
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          (fun j => coordinatePresentationWeight (σ := σ) (b j))) D
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          (fun j => coordinatePresentationWeight (σ := σ) (b j))) hD β hβ 0) ≫
      (coordinateNativeOriginalPresentationPolynomialTopCokernelIso a b D hD c β hc hβ honto hex n hcard).hom =
    (coordinateNativeOriginalFreeTopHomologyDualIso b n hcard).hom ≫
      cokernel.π (coordinateCanonicalGradedPolynomialDualMatrix a b (coordinatePresentationPolynomialEntry a b c hc)) := by
  rw [← coordinateNativeOriginalPresentationTopCokernelIso_quotient a b D hD c β hc hβ honto hex n hcard]
  simp [coordinateNativeOriginalPresentationPolynomialTopCokernelIso,cokernel.map]

end MvPolynomial
