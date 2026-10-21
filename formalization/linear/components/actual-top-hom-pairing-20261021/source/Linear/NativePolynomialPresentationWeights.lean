module
public import Linear.NativeShiftedFreeSheafScalarMatrix
public import Linear.NativePolynomialEntryValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
variable {K : Type} [Field K] {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual original free-module weight corresponding to the negative
coordinate twist used in native top-degree duality. -/
def coordinatePresentationWeight (a : ℕ) : ℤ := (a : ℤ)+Fintype.card σ

theorem coordinatePresentationWeight_neg (a : ℕ) :
    -coordinatePresentationWeight (σ := σ) a = -(a:ℤ)-Fintype.card σ := by
  unfold coordinatePresentationWeight
  omega

/-- Only genuine arithmetic equality identifies the original free
coordinate sheaf with the already published coordinate integer twist. -/
def coordinateNativePresentationWeightIso (a : ℕ) :
    LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K))
      (-coordinatePresentationWeight (σ := σ) a) ≅
    coordinateNativeIntegerTwist (K := K) (σ := σ) (-(a:ℤ)-Fintype.card σ) :=
  eqToIso (congrArg (fun d => coordinateNativeIntegerTwist (K := K) (σ := σ) d)
    (coordinatePresentationWeight_neg (σ := σ) a))

/-- Actual original prime values are unchanged by the weight comparison. -/
theorem coordinateNativePresentationWeightIso_hom_value (a : ℕ)
    (U : (Opens (ProjectiveSpectrum.top (homogeneousSubmodule σ K)))ᵒᵖ)
    (s : LinearStudy.nativeProjectiveModuleSections (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K))
      (-coordinatePresentationWeight (σ := σ) a) U) (x : U.unop) :
    ((((coordinateNativePresentationWeightIso (K := K) (σ := σ) a).hom).val.app U) s).1 x = s.1 x := by
  exact LinearStudy.nativeRingIntegerTwistDegreeCast_value (homogeneousSubmodule σ K)
    (coordinatePresentationWeight_neg (σ := σ) a) U s x

/-- The inverse original comparison also preserves every original value. -/
theorem coordinateNativePresentationWeightIso_inv_value (a : ℕ)
    (U : (Opens (ProjectiveSpectrum.top (homogeneousSubmodule σ K)))ᵒᵖ)
    (s : LinearStudy.nativeProjectiveModuleSections (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K))
      (-(a:ℤ)-Fintype.card σ) U) (x : U.unop) :
    ((((coordinateNativePresentationWeightIso (K := K) (σ := σ) a).inv).val.app U) s).1 x = s.1 x := by
  exact LinearStudy.nativeRingIntegerTwistDegreeCast_value (homogeneousSubmodule σ K)
    (coordinatePresentationWeight_neg (σ := σ) a).symm U s x

variable {I J : Type} [DecidableEq I]
variable (a : I → ℕ) (b : J → ℕ)
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (hh : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun i => coordinatePresentationWeight (σ := σ) (a i)) d →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) d)

include hh in
/-- The homogeneous polynomial entry is extracted from the ACTUAL original
relation map. Its degree is derived, including the proved negative case. -/
theorem coordinatePresentationPolynomialEntry_mem (i : I) (j : J) :
    LinearStudy.integerShiftedFreeMapEntry c i j ∈ homogeneousSubmodule σ K (a i-b j) := by
  by_cases h : b j ≤ a i
  · have hweight : coordinatePresentationWeight (σ := σ) (b j) ≤
        coordinatePresentationWeight (σ := σ) (a i) := by
      unfold coordinatePresentationWeight
      omega
    have hd : (coordinatePresentationWeight (σ := σ) (a i)-
        coordinatePresentationWeight (σ := σ) (b j)).toNat = a i-b j := by
      unfold coordinatePresentationWeight
      omega
    simpa only [hd] using LinearStudy.integerShiftedFreeMapEntry_mem_nat
      (homogeneousSubmodule σ K) (fun i => coordinatePresentationWeight (σ := σ) (a i))
      (fun j => coordinatePresentationWeight (σ := σ) (b j)) c hh i j hweight
  · have hweight : coordinatePresentationWeight (σ := σ) (a i) <
        coordinatePresentationWeight (σ := σ) (b j) := by
      unfold coordinatePresentationWeight
      omega
    rw [LinearStudy.integerShiftedFreeMapEntry_eq_zero (homogeneousSubmodule σ K)
      (fun i => coordinatePresentationWeight (σ := σ) (a i))
      (fun j => coordinatePresentationWeight (σ := σ) (b j)) c hh i j hweight]
    exact (homogeneousSubmodule σ K (a i-b j)).zero_mem

/-- Original homogeneous entry c(e_i)_j, not a separately chosen polynomial. -/
def coordinatePresentationPolynomialEntry (i : I) (j : J) :
    homogeneousSubmodule σ K (a i-b j) :=
  ⟨LinearStudy.integerShiftedFreeMapEntry c i j,
    coordinatePresentationPolynomialEntry_mem a b c hh i j⟩

end MvPolynomial
