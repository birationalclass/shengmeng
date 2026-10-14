module
public import Linear.NativeOriginalPolynomialRelationEntry
public import Linear.NativePolynomialMatrixTopDuality
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

/-- The comparison is built from the ORIGINAL free coordinate bicone
and genuine weight equality isomorphisms, before any duality is used. -/
def coordinateNativeOriginalFreePresentationIso {L : Type} [Fintype L] [DecidableEq L]
    (a : L → ℕ) :
    LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K)
      (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
        (fun i => coordinatePresentationWeight (σ := σ) (a i)))
      (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
        (fun i => coordinatePresentationWeight (σ := σ) (a i))) 0 ≅
    (⨁ fun i => coordinateNativeIntegerTwist (K := K) (σ := σ) (-(a i:ℤ)-Fintype.card σ)) :=
  (LinearStudy.nativeShiftedFreeSheafBiproductIso (homogeneousSubmodule σ K)
    (fun i => coordinatePresentationWeight (σ := σ) (a i))).trans
      (biproduct.mapIso (fun i => coordinateNativePresentationWeightIso (K := K) (σ := σ) (a i)))

omit [LinearOrder σ] in
/-- Original incoming coordinate map under the constructed comparison. -/
theorem coordinateNativeOriginalFreePresentationIso_inclusion {L : Type}
    [Fintype L] [DecidableEq L] (a : L → ℕ) (i : L) :
    biproduct.ι (fun j => coordinateNativeIntegerTwist (K := K) (σ := σ)
      (-(a j:ℤ)-Fintype.card σ)) i ≫ (coordinateNativeOriginalFreePresentationIso a).inv =
    (coordinateNativePresentationWeightIso (K := K) (σ := σ) (a i)).inv ≫
      LinearStudy.nativeShiftedFreeCoordinateSheafInclusion (homogeneousSubmodule σ K)
        (fun j => coordinatePresentationWeight (σ := σ) (a j)) i := by
  simp only [coordinateNativeOriginalFreePresentationIso,Iso.trans_inv,biproduct.mapIso_inv,
    biproduct.ι_map_assoc]
  erw [LinearStudy.nativeShiftedFreeSheafBiproductIso_inclusion (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (a j)) i]

omit [LinearOrder σ] in
/-- Original outgoing coordinate map under the constructed comparison. -/
theorem coordinateNativeOriginalFreePresentationIso_projection {L : Type}
    [Fintype L] [DecidableEq L] (a : L → ℕ) (i : L) :
    (coordinateNativeOriginalFreePresentationIso a).hom ≫
      biproduct.π (fun j => coordinateNativeIntegerTwist (K := K) (σ := σ)
        (-(a j:ℤ)-Fintype.card σ)) i =
    LinearStudy.nativeShiftedFreeCoordinateSheafProjection (homogeneousSubmodule σ K)
      (fun j => coordinatePresentationWeight (σ := σ) (a j)) i ≫
    (coordinateNativePresentationWeightIso (K := K) (σ := σ) (a i)).hom := by
  simp only [coordinateNativeOriginalFreePresentationIso,Iso.trans_hom,biproduct.mapIso_hom,
    Category.assoc,biproduct.map_π]
  simp only [← Category.assoc]
  erw [LinearStudy.nativeShiftedFreeSheafBiproductIso_projection (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (a j)) i]

/-- For an ACTUAL original homogeneous free relation c with the stated
weights,the ORIGINAL sheafified c is the already published coordinate
polynomial matrix under the constructed original comparisons. All entries
are extracted as c(e_i)_j and their correct degrees,negative zeros and
multiplication comparisons are proved. No matrix identity is assumed. -/
theorem coordinateNativeOriginalFreeRelation_polynomialMatrix {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (a : I → ℕ) (b : J → ℕ)
    (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
    (hh : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
      x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
        (fun i => coordinatePresentationWeight (σ := σ) (a i)) d →
      c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
        (fun j => coordinatePresentationWeight (σ := σ) (b j)) d) :
    (coordinateNativeOriginalFreePresentationIso a).inv ≫
      LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          (fun i => coordinatePresentationWeight (σ := σ) (a i)))
        (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
          (fun j => coordinatePresentationWeight (σ := σ) (b j)))
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          (fun i => coordinatePresentationWeight (σ := σ) (a i)))
        (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
          (fun j => coordinatePresentationWeight (σ := σ) (b j))) c hh 0 ≫
      (coordinateNativeOriginalFreePresentationIso b).hom =
    coordinateNativeGradedPolynomialMatrix a b (coordinatePresentationPolynomialEntry a b c hh) := by
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simp only [← Category.assoc]
  erw [coordinateNativeOriginalFreePresentationIso_inclusion a i]
  simp only [Category.assoc]
  erw [coordinateNativeOriginalFreePresentationIso_projection b j]
  rw [coordinateNativeGradedPolynomialMatrix,biproduct.ι_matrix_assoc,biproduct.lift_π]
  change (coordinateNativePresentationWeightIso (K := K) (σ := σ) (a i)).inv ≫
    coordinateNativeOriginalFreeRelationComponent a b c hh i j ≫
    (coordinateNativePresentationWeightIso (K := K) (σ := σ) (b j)).hom = _
  exact coordinateNativeOriginalFreeRelationComponent_polynomial a b c hh i j

end MvPolynomial
