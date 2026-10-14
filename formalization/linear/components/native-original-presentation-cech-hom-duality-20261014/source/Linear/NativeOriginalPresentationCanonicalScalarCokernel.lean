module
public import Linear.ProjectiveGradedDualCoefficientCokernel
public import Linear.NativeOriginalPresentationCoordinateCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
variable {K M : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
variable [IsScalarTower K (MvPolynomial σ K) M]
attribute [local instance] MvPolynomial.gradedAlgebra

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

/-- The ACTUAL original presentation's top ordered-Cech homology,
restricted by the original canonical scalar map,is the ACTUAL original
K-polynomial dual matrix cokernel. The native geometric presentation,
its actual original entries,and the whole canonical scalar cokernel
comparison are constructed;no Cech/cokernel comparison is supplied. -/
def coordinateNativeOriginalPresentationKPolynomialTopCokernelIso :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
        (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K) D hD 0)) ≅
      cokernel (projectiveHomogeneousGradedPolynomialDualMatrix a b
        (coordinatePresentationPolynomialEntry a b c hc)) :=
  ((ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).mapIso
    (coordinateNativeOriginalPresentationPolynomialTopCokernelIso
      a b D hD c β hc hβ honto hex n hcard)).trans
    (coordinateCanonicalGradedDualCoefficientCokernelIso K a b
      (coordinatePresentationPolynomialEntry a b c hc)).symm

/-- The above ACTUAL original Cech comparison respects the ORIGINAL
quotient beta after canonical scalar restriction,with original matrix
quotient pi_K and original free coefficient comparison. -/
theorem coordinateNativeOriginalPresentationKPolynomialTopCokernelIso_quotient :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
          (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
            (fun j => coordinatePresentationWeight (σ := σ) (b j))) D
          (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
            (fun j => coordinatePresentationWeight (σ := σ) (b j))) hD β hβ 0)) ≫
      (coordinateNativeOriginalPresentationKPolynomialTopCokernelIso
        a b D hD c β hc hβ honto hex n hcard).hom =
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      (coordinateNativeOriginalFreeTopHomologyDualIso b n hcard).hom ≫
        (coordinateCanonicalFiniteHomogeneousDualCoefficientIso K b).inv ≫
          cokernel.π (projectiveHomogeneousGradedPolynomialDualMatrix a b
            (coordinatePresentationPolynomialEntry a b c hc)) := by
  let F := ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let p := coordinatePresentationPolynomialEntry a b c hc
  let κ := coordinateCanonicalGradedDualCoefficientCokernelIso K a b p
  let Cb := coordinateCanonicalFiniteHomogeneousDualCoefficientIso (σ := σ) K b
  have hπ : F.map (cokernel.π (coordinateCanonicalGradedPolynomialDualMatrix a b p)) ≫ κ.inv =
      Cb.inv ≫ cokernel.π (projectiveHomogeneousGradedPolynomialDualMatrix a b p) := by
    apply (cancel_mono κ.hom).1
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    erw [coordinateCanonicalGradedDualCoefficientCokernelIso_quotient K a b p]
    simp [F,Cb,← Category.assoc]
  unfold coordinateNativeOriginalPresentationKPolynomialTopCokernelIso
  simp only [Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom]
  rw [← Category.assoc,← Functor.map_comp]
  erw [coordinateNativeOriginalPresentationPolynomialTopCokernelIso_quotient
    a b D hD c β hc hβ honto hex n hcard]
  rw [Functor.map_comp,Category.assoc]
  exact congrArg (fun t => F.map (coordinateNativeOriginalFreeTopHomologyDualIso b n hcard).hom ≫ t) hπ

end MvPolynomial
