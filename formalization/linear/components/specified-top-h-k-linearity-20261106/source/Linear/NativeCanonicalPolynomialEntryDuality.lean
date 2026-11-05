module
public import Linear.NativeIntegerFreeHomDuality
public import Linear.ProjectiveOriginalGradedPolynomialMultiply
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- The actual original natural top Cech comparison under the ACTUAL
canonical GammaSpec scalar restriction,with ORIGINAL K-dual coefficients. -/
def coordinateNativeCanonicalTopHomologyDualIso (a n : ℕ)
    (hcard : Fintype.card σ=n+2) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (-(a:ℤ)-Fintype.card σ))) ≅
    ModuleCat.of K (Module.Dual K (homogeneousSubmodule σ K a)) :=
  ((ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).mapIso
    (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) a n hcard)).trans
      (coordinateCanonicalHomogeneousDualCoefficientIso (σ := σ) K a).symm

/-- The ORIGINAL polynomial entry square is preserved by the ACTUAL
canonical scalar restriction. Neither a coefficient square nor a chosen
Cech isomorphism is supplied as an input. -/
theorem coordinateNativeCanonicalTopHomologyDualIso_polynomial
    (a b n : ℕ) (hcard : Fintype.card σ=n+2)
    (p : homogeneousSubmodule σ K (a-b)) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (coordinateNativeGradedPolynomialEntry a b p)) ≫
      (coordinateNativeCanonicalTopHomologyDualIso b n hcard).hom =
    (coordinateNativeCanonicalTopHomologyDualIso a n hcard).hom ≫
      projectiveHomogeneousGradedPolynomialDualEntry a b p := by
  let F := ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  have hm := congrArg F.map
    (coordinateNativeGradedPolynomialEntry_top_duality a b n hcard p)
  simp only [Functor.map_comp] at hm
  have hp := coordinateCanonicalHomogeneousDualCoefficientIso_gradedEntry K a b p
  apply (cancel_mono (coordinateCanonicalHomogeneousDualCoefficientIso (σ := σ) K b).hom).1
  simp only [coordinateNativeCanonicalTopHomologyDualIso,Iso.trans_hom,
    Functor.mapIso_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [hp]
  simp only [Iso.inv_hom_id_assoc]
  exact hm

end MvPolynomial
