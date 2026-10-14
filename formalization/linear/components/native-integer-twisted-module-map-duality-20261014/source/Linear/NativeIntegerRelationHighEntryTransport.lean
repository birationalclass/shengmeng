module
public import Linear.ProjectiveIntegerHighWeightTransport
public import Linear.IntegerShiftedFreeGeneralRelationBiproduct
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] LinearStudy.nativeProjectiveAtPrimeModuleScalar

theorem coordinateNativeHighIntegerWeightSheafIso_hom_value (w : ℤ) (a : ℕ)
    (ha : w=(a:ℤ)+Fintype.card σ)
    (U : (Opens (ProjectiveSpectrum.top (homogeneousSubmodule σ K)))ᵒᵖ)
    (s : LinearStudy.nativeProjectiveModuleSections (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K)) (-w) U)
    (x : U.unop) :
    ((((coordinateNativeHighIntegerWeightSheafIso w a ha).hom).val.app U) s).1 x=s.1 x := by
  exact coordinateNativeSheafDegreeCast_value (show -w=-(a:ℤ)-Fintype.card σ by omega) U s x

theorem coordinateNativeHighIntegerWeightSheafIso_inv_value (w : ℤ) (a : ℕ)
    (ha : w=(a:ℤ)+Fintype.card σ)
    (U : (Opens (ProjectiveSpectrum.top (homogeneousSubmodule σ K)))ᵒᵖ)
    (s : LinearStudy.nativeProjectiveModuleSections (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K))
      (-(a:ℤ)-Fintype.card σ) U) (x : U.unop) :
    ((((coordinateNativeHighIntegerWeightSheafIso w a ha).inv).val.app U) s).1 x=s.1 x := by
  exact coordinateNativeSheafDegreeCast_value (show -(a:ℤ)-Fintype.card σ=-w by omega) U s x

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (z : I → ℤ) (w : J → ℤ)
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (hc : ∀ t : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) z t →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) w t)

include hc in
/-- ONLY the selected original source and target weights are high.
Their original polynomial entry has the correct original natural degree.
Other weights remain arbitrary integers;negative multiplying entries
are derived zero from original homogeneity. -/
theorem coordinateIntegerHighRelationPolynomial_mem (i : I) (j : J) (a b : ℕ)
    (hi : z i=(a:ℤ)+Fintype.card σ) (hj : w j=(b:ℤ)+Fintype.card σ) :
    LinearStudy.integerShiftedFreeMapEntry c i j ∈ homogeneousSubmodule σ K (a-b) := by
  by_cases hab : b≤a
  · have hw : w j≤z i := by omega
    have hd : (z i-w j).toNat=a-b := by omega
    simpa only [hd] using LinearStudy.integerShiftedFreeMapEntry_mem_nat
      (homogeneousSubmodule σ K) z w c hc i j hw
  · have hw : z i<w j := by omega
    rw [LinearStudy.integerShiftedFreeMapEntry_eq_zero (homogeneousSubmodule σ K) z w c hc i j hw]
    exact (homogeneousSubmodule σ K (a-b)).zero_mem

/-- The original p_ij=c(e_i)_j,not a separately supplied polynomial. -/
def coordinateIntegerHighRelationPolynomial (i : I) (j : J) (a b : ℕ)
    (hi : z i=(a:ℤ)+Fintype.card σ) (hj : w j=(b:ℤ)+Fintype.card σ) :
    homogeneousSubmodule σ K (a-b) :=
  ⟨LinearStudy.integerShiftedFreeMapEntry c i j,
    coordinateIntegerHighRelationPolynomial_mem z w c hc i j a b hi hj⟩

/-- Actual ORIGINAL scalar entry agrees with original natural polynomial
multiplication under ONLY the two selected genuine degree transports. -/
theorem coordinateIntegerHighRelationSheafEntry_transport (i : I) (j : J) (a b : ℕ)
    (hi : z i=(a:ℤ)+Fintype.card σ) (hj : w j=(b:ℤ)+Fintype.card σ) :
    (coordinateNativeHighIntegerWeightSheafIso (z i) a hi).inv ≫
      LinearStudy.nativeShiftedFreeSheafScalarMatrixEntry (homogeneousSubmodule σ K) z w c hc i j ≫
      (coordinateNativeHighIntegerWeightSheafIso (w j) b hj).hom =
    coordinateNativeGradedPolynomialEntry a b
      (coordinateIntegerHighRelationPolynomial z w c hc i j a b hi hj) := by
  by_cases hab : b≤a
  · have hw : w j≤z i := by omega
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext x
    let s' := (((coordinateNativeHighIntegerWeightSheafIso (z i) a hi).inv).val.app U) s
    change ((((coordinateNativeHighIntegerWeightSheafIso (w j) b hj).hom).val.app U)
      (((LinearStudy.nativeShiftedFreeSheafScalarMatrixEntry
        (homogeneousSubmodule σ K) z w c hc i j).val.app U) s')).1 x = _
    calc
      _ = (((LinearStudy.nativeShiftedFreeSheafScalarMatrixEntry
          (homogeneousSubmodule σ K) z w c hc i j).val.app U) s').1 x :=
        coordinateNativeHighIntegerWeightSheafIso_hom_value (w j) b hj U _ x
      _ = LinearStudy.integerShiftedFreeMapEntry c i j • s'.1 x := by
        simp only [LinearStudy.nativeShiftedFreeSheafScalarMatrixEntry,dite_eq_left hw]
        exact LinearStudy.nativeShiftedFreeSheafNonnegativeEntry_value
          (homogeneousSubmodule σ K) z w c hc i j hw U s' x
      _ = LinearStudy.integerShiftedFreeMapEntry c i j • s.1 x :=
        congrArg (fun v => LinearStudy.integerShiftedFreeMapEntry c i j • v)
          (coordinateNativeHighIntegerWeightSheafIso_inv_value (z i) a hi U s x)
      _ = _ := (coordinateNativeGradedPolynomialEntry_value a b hab
        (coordinateIntegerHighRelationPolynomial z w c hc i j a b hi hj) U s x).symm
  · have hw : ¬ w j≤z i := by omega
    rw [LinearStudy.nativeShiftedFreeSheafScalarMatrixEntry,dite_eq_right hw,zero_comp,comp_zero]
    exact (coordinateNativeGradedPolynomialEntry_of_lt a b _ (lt_of_not_ge hab)).symm

/-- The ACTUAL ORIGINAL Delta coefficient entry has exactly the same
original natural multiplication under the corresponding ORIGINAL piece
transports. No coefficient-entry square is an input. -/
theorem coordinateIntegerHighRelationCoefficientEntry_transport (i : I) (j : J) (a b : ℕ)
    (hi : z i=(a:ℤ)+Fintype.card σ) (hj : w j=(b:ℤ)+Fintype.card σ) :
    (projectiveHighIntegerWeightPieceEquiv (K := K) (w j) b hj).toModuleIso.inv ≫
      LinearStudy.integerShiftedFreeDualRelationEntry (homogeneousSubmodule σ K)
        z w c hc (-(Fintype.card σ:ℤ)) i j ≫
      (projectiveHighIntegerWeightPieceEquiv (K := K) (z i) a hi).toModuleIso.hom =
    projectiveHomogeneousGradedPolynomialMultiplyEntry a b
      (coordinateIntegerHighRelationPolynomial z w c hc i j a b hi hj) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  change (projectiveHighIntegerWeightPieceEquiv (K := K) (z i) a hi
    (LinearStudy.integerShiftedFreeDualRelationEntry (homogeneousSubmodule σ K)
      z w c hc (-(Fintype.card σ:ℤ)) i j
      ((projectiveHighIntegerWeightPieceEquiv (K := K) (w j) b hj).symm q))).1 = _
  rw [projectiveHighIntegerWeightPieceEquiv_apply,LinearStudy.integerShiftedFreeDualRelationEntry_value]
  have hq : ((projectiveHighIntegerWeightPieceEquiv (K := K) (w j) b hj).symm q).1=q.1 := rfl
  rw [hq]
  by_cases hab : b≤a
  · exact (projectiveHomogeneousGradedPolynomialMultiplyEntry_coe a b
      (coordinateIntegerHighRelationPolynomial z w c hc i j a b hi hj) q hab).symm
  · have hw : z i<w j := by omega
    rw [projectiveHomogeneousGradedPolynomialMultiplyEntry_of_lt _ _ _ (lt_of_not_ge hab),
      LinearStudy.integerShiftedFreeMapEntry_eq_zero (homogeneousSubmodule σ K) z w c hc i j hw]
    simp

end MvPolynomial
