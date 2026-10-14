module
public import Linear.NativeOriginalPolynomialRelationMatrix
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- Top ordered-Cech duality for the ACTUAL original weighted free
associated sheaf,using its constructed original coordinate comparison,
not replacing its cohomology map by a duality-coordinate definition. -/
def coordinateNativeOriginalFreeTopHomologyDualIso {L : Type}
    [Fintype L] [DecidableEq L] (a : L → ℕ) (n : ℕ) (hc : Fintype.card σ=n+2) :
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
      (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K)
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          (fun i => coordinatePresentationWeight (σ := σ) (a i)))
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          (fun i => coordinatePresentationWeight (σ := σ) (a i))) 0) ≅
    (⨁ fun i => ModuleCat.of (coordinateCanonicalBaseRing K)
      (Module.Dual (coordinateCanonicalBaseRing K)
        (homogeneousSubmodule σ (coordinateCanonicalBaseRing K) (a i)))) :=
  ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).mapIso
    (coordinateNativeOriginalFreePresentationIso a)).trans
      (coordinateNativeFiniteTwistTopHomologyDualIso (K := K) (σ := σ) a n hc)

/-- The ACTUAL top ordered-Cech homology map of the ORIGINAL free
relation c is the already verified canonical polynomial transpose matrix
under constructed original free dualities. Entries come from original c;
no whole-matrix or cohomology-naturality premise is supplied. -/
theorem coordinateNativeOriginalFreeRelation_top_duality {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (a : I → ℕ) (b : J → ℕ)
    (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
    (hh : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
      x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
        (fun i => coordinatePresentationWeight (σ := σ) (a i)) d →
      c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
        (fun j => coordinatePresentationWeight (σ := σ) (b j)) d)
    (n : ℕ) (hc : Fintype.card σ=n+2) :
    (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
      (LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          (fun i => coordinatePresentationWeight (σ := σ) (a i)))
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          (fun j => coordinatePresentationWeight (σ := σ) (b j)))
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          (fun i => coordinatePresentationWeight (σ := σ) (a i)))
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          (fun j => coordinatePresentationWeight (σ := σ) (b j))) c hh 0) ≫
      (coordinateNativeOriginalFreeTopHomologyDualIso b n hc).hom =
    (coordinateNativeOriginalFreeTopHomologyDualIso a n hc).hom ≫
      coordinateCanonicalGradedPolynomialDualMatrix a b (coordinatePresentationPolynomialEntry a b c hh) := by
  let C := LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
    (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
      (fun i => coordinatePresentationWeight (σ := σ) (a i)))
    (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
      (fun j => coordinatePresentationWeight (σ := σ) (b j)))
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
      (fun i => coordinatePresentationWeight (σ := σ) (a i)))
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
      (fun j => coordinatePresentationWeight (σ := σ) (b j))) c hh 0
  have he : C ≫ (coordinateNativeOriginalFreePresentationIso b).hom =
      (coordinateNativeOriginalFreePresentationIso a).hom ≫
        coordinateNativeGradedPolynomialMatrix a b (coordinatePresentationPolynomialEntry a b c hh) := by
    have hm := congrArg (fun f => (coordinateNativeOriginalFreePresentationIso a).hom ≫ f)
      (coordinateNativeOriginalFreeRelation_polynomialMatrix a b c hh)
    simpa only [← Category.assoc,Iso.hom_inv_id,Category.id_comp] using hm
  unfold coordinateNativeOriginalFreeTopHomologyDualIso
  simp only [Iso.trans_hom,Functor.mapIso_hom]
  rw [← Category.assoc,← Functor.map_comp,he,Functor.map_comp,Category.assoc]
  rw [coordinateNativeGradedPolynomialMatrix_top_duality a b n hc]
  simp only [Category.assoc]

end MvPolynomial
