module
public import Linear.NativeGradedPolynomialEntry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [Fintype σ] [LinearOrder σ] in
/-- The published original coordinate sheaf degree cast preserves values
at every original prime on every original open. -/
theorem coordinateNativeSheafDegreeCast_value {d d' : ℤ} (h : d=d')
    (U : (Opens (ProjectiveSpectrum.top (homogeneousSubmodule σ K)))ᵒᵖ)
    (s : LinearStudy.nativeProjectiveModuleSections (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K)) d U)
    (x : U.unop) :
    (((coordinateNativeSheafDegreeCast (K := K) (σ := σ) h).val.app U) s).1 x = s.1 x := by
  cases h
  rfl

/-- Actual complementary multiplication, including its actual target
integer-degree cast, has the original polynomial value on every open. -/
theorem coordinateNativeComplementaryPolynomialSheafMap_value (l m : ℕ)
    (p : homogeneousSubmodule σ K l)
    (U : (Opens (ProjectiveSpectrum.top (homogeneousSubmodule σ K)))ᵒᵖ)
    (s : LinearStudy.nativeProjectiveModuleSections (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K))
      (-((l+m:ℕ):ℤ)-Fintype.card σ) U) (x : U.unop) :
    (((coordinateNativeComplementaryPolynomialSheafMap l m p).val.app U) s).1 x =
      p.1 • s.1 x := by
  change (((coordinateNativeSheafDegreeCast (projectiveComplementaryShiftDegree (σ := σ) l m)).val.app U)
    (((coordinateNativePolynomialMultiplication l p (-((l+m:ℕ):ℤ)-Fintype.card σ)).val.app U) s)).1 x = _
  exact (coordinateNativeSheafDegreeCast_value (projectiveComplementaryShiftDegree (σ := σ) l m)
    U _ x).trans (coordinateNativePolynomialMultiplication_value l p
      (-((l+m:ℕ):ℤ)-Fintype.card σ) U s x)

/-- Actual varied-degree multiplication has its original polynomial value;
both degree equality transports are the original sheaf transports. -/
theorem coordinateNativeDegreePolynomialSheafMap_value (a b l : ℕ) (h : a=l+b)
    (p : homogeneousSubmodule σ K l)
    (U : (Opens (ProjectiveSpectrum.top (homogeneousSubmodule σ K)))ᵒᵖ)
    (s : LinearStudy.nativeProjectiveModuleSections (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K))
      (-(a:ℤ)-Fintype.card σ) U) (x : U.unop) :
    (((coordinateNativeDegreePolynomialSheafMap a b l h p).val.app U) s).1 x = p.1 • s.1 x := by
  subst a
  simp only [coordinateNativeDegreePolynomialSheafMap,coordinateNativeSheafDegreeCast,
    eqToHom_refl,Category.id_comp]
  exact coordinateNativeComplementaryPolynomialSheafMap_value l b p U s x

/-- In the nonnegative-degree case,the already published original matrix
entry is original polynomial multiplication at every original point. -/
theorem coordinateNativeGradedPolynomialEntry_value (a b : ℕ) (h : b≤a)
    (p : homogeneousSubmodule σ K (a-b))
    (U : (Opens (ProjectiveSpectrum.top (homogeneousSubmodule σ K)))ᵒᵖ)
    (s : LinearStudy.nativeProjectiveModuleSections (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K))
      (-(a:ℤ)-Fintype.card σ) U) (x : U.unop) :
    (((coordinateNativeGradedPolynomialEntry a b p).val.app U) s).1 x = p.1 • s.1 x := by
  simp only [coordinateNativeGradedPolynomialEntry,dite_eq_left h]
  exact coordinateNativeDegreePolynomialSheafMap_value a b (a-b)
    (Nat.sub_add_cancel h).symm p U s x

end MvPolynomial
