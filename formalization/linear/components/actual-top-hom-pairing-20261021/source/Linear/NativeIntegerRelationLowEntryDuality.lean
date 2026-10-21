module
public import Linear.NativeIntegerFreeFamilyHomDuality
public import Linear.IntegerShiftedFreeGeneralRelationBiproduct
public import Linear.NativeShiftedFreeSheafScalarMatrix
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open CategoryTheory CategoryTheory.Limits
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (z : I → ℤ) (w : J → ℤ)
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (hc : ∀ t : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) z t →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) w t)

/-- The ACTUAL ORIGINAL scalar/relation-entry square commutes when the
original source weight is below N. Its actual original Cech object is zero
by the proved Laurent contraction,not by an assumed comparison square. -/
theorem coordinateNativeIntegerRelationEntry_duality_of_source_lt
    (i : I) (j : J) (hi : z i<(Fintype.card σ:ℤ)) (n : ℕ)
    (hcard : Fintype.card σ=n+2) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeShiftedFreeSheafScalarMatrixEntry
          (homogeneousSubmodule σ K) z w c hc i j)) ≫
      (coordinateNativeIntegerWeightHomDualIso (w j) n hcard).hom =
    (coordinateNativeIntegerWeightHomDualIso (z i) n hcard).hom ≫
      ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualRelationEntry
        (homogeneousSubmodule σ K) z w c hc (-(Fintype.card σ:ℤ)) i j).hom.dualMap := by
  exact (Functor.map_isZero
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom)
    (coordinateNativeIntegerWeight_cechHomology_isZero_of_lt_card
      (K := K) (z i) hi n)).eq_of_src _ _

/-- The same ORIGINAL square commutes when the original target weight
is below N,because its actual coefficient dual is the dual of zero. -/
theorem coordinateNativeIntegerRelationEntry_duality_of_target_lt
    (i : I) (j : J) (hj : w j<(Fintype.card σ:ℤ)) (n : ℕ)
    (hcard : Fintype.card σ=n+2) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (LinearStudy.nativeShiftedFreeSheafScalarMatrixEntry
          (homogeneousSubmodule σ K) z w c hc i j)) ≫
      (coordinateNativeIntegerWeightHomDualIso (w j) n hcard).hom =
    (coordinateNativeIntegerWeightHomDualIso (z i) n hcard).hom ≫
      ModuleCat.ofHom (LinearStudy.integerShiftedFreeDualRelationEntry
        (homogeneousSubmodule σ K) z w c hc (-(Fintype.card σ:ℤ)) i j).hom.dualMap := by
  exact (projectiveIntegerHomogeneousDual_isZero_of_neg (K := K) (σ := σ)
    (w j-(Fintype.card σ:ℤ)) (by omega)).eq_of_tgt _ _

end MvPolynomial
