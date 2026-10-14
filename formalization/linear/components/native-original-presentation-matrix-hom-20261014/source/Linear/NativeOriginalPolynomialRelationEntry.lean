module
public import Linear.NativePolynomialPresentationWeights
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable {I J : Type} [DecidableEq I] [DecidableEq J]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] LinearStudy.nativeProjectiveAtPrimeModuleScalar
variable (a : I → ℕ) (b : J → ℕ)
variable (c : (I → MvPolynomial σ K) →ₗ[MvPolynomial σ K] (J → MvPolynomial σ K))
variable (hh : ∀ d : ℤ, ∀ x : I → MvPolynomial σ K,
  x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun i => coordinatePresentationWeight (σ := σ) (a i)) d →
  c x ∈ LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) d)

/-- Original coordinate component, made from ORIGINAL inclusion,the
original degree-zero sheafified relation c,and ORIGINAL projection. -/
def coordinateNativeOriginalFreeRelationComponent (i : I) (j : J) :
    LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K))
      (-coordinatePresentationWeight (σ := σ) (a i)) ⟶
    LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K))
      (-coordinatePresentationWeight (σ := σ) (b j)) :=
  LinearStudy.nativeShiftedFreeCoordinateSheafInclusion (homogeneousSubmodule σ K)
    (fun i => coordinatePresentationWeight (σ := σ) (a i)) i ≫
  LinearStudy.nativeProjectiveDegreeZeroSheafMap (homogeneousSubmodule σ K)
    (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
      (fun i => coordinatePresentationWeight (σ := σ) (a i)))
    (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K)
      (fun j => coordinatePresentationWeight (σ := σ) (b j)))
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
      (fun i => coordinatePresentationWeight (σ := σ) (a i)))
    (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K)
      (fun j => coordinatePresentationWeight (σ := σ) (b j))) c hh 0 ≫
  LinearStudy.nativeShiftedFreeCoordinateSheafProjection (homogeneousSubmodule σ K)
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) j

omit [LinearOrder σ] in
/-- Actual original-prime value of this original coordinate component. -/
theorem coordinateNativeOriginalFreeRelationComponent_value (i : I) (j : J)
    (U : (Opens (ProjectiveSpectrum.top (homogeneousSubmodule σ K)))ᵒᵖ)
    (s : LinearStudy.nativeProjectiveModuleSections (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K))
      (-coordinatePresentationWeight (σ := σ) (a i)) U) (x : U.unop) :
    (((coordinateNativeOriginalFreeRelationComponent a b c hh i j).val.app U) s).1 x =
      LinearStudy.integerShiftedFreeMapEntry c i j • s.1 x := by
  exact LinearStudy.nativeShiftedFreeSheaf_matrixEntry_value (homogeneousSubmodule σ K) c
    (fun i => coordinatePresentationWeight (σ := σ) (a i))
    (fun j => coordinatePresentationWeight (σ := σ) (b j)) hh i j U s x

/-- Under genuine original weight comparisons,the coordinate component
of the ACTUAL original relation map equals the already published actual
polynomial sheaf entry,with polynomial extracted from c. The negative
case is derived zero. No entry comparison is assumed. -/
theorem coordinateNativeOriginalFreeRelationComponent_polynomial (i : I) (j : J) :
    (coordinateNativePresentationWeightIso (K := K) (σ := σ) (a i)).inv ≫
      coordinateNativeOriginalFreeRelationComponent a b c hh i j ≫
      (coordinateNativePresentationWeightIso (K := K) (σ := σ) (b j)).hom =
    coordinateNativeGradedPolynomialEntry (a i) (b j)
      (coordinatePresentationPolynomialEntry a b c hh i j) := by
  by_cases h : b j ≤ a i
  · apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext x
    let s' := (((coordinateNativePresentationWeightIso (K := K) (σ := σ) (a i)).inv).val.app U) s
    change ((((coordinateNativePresentationWeightIso (K := K) (σ := σ) (b j)).hom).val.app U)
      (((coordinateNativeOriginalFreeRelationComponent a b c hh i j).val.app U) s')).1 x = _
    calc
      _ = (((coordinateNativeOriginalFreeRelationComponent a b c hh i j).val.app U) s').1 x :=
        coordinateNativePresentationWeightIso_hom_value (b j) U _ x
      _ = LinearStudy.integerShiftedFreeMapEntry c i j • s'.1 x :=
        coordinateNativeOriginalFreeRelationComponent_value a b c hh i j U s' x
      _ = LinearStudy.integerShiftedFreeMapEntry c i j • s.1 x :=
        congrArg (fun v => LinearStudy.integerShiftedFreeMapEntry c i j • v)
          (coordinateNativePresentationWeightIso_inv_value (a i) U s x)
      _ = _ := (coordinateNativeGradedPolynomialEntry_value (a i) (b j) h
        (coordinatePresentationPolynomialEntry a b c hh i j) U s x).symm
  · have hw : coordinatePresentationWeight (σ := σ) (a i) <
        coordinatePresentationWeight (σ := σ) (b j) := by
      unfold coordinatePresentationWeight
      omega
    have hz : coordinateNativeOriginalFreeRelationComponent a b c hh i j = 0 :=
      LinearStudy.nativeShiftedFreeSheaf_matrixEntry_zero (homogeneousSubmodule σ K)
        (fun i => coordinatePresentationWeight (σ := σ) (a i))
        (fun j => coordinatePresentationWeight (σ := σ) (b j)) c hh i j hw
    rw [hz,zero_comp,comp_zero]
    exact (coordinateNativeGradedPolynomialEntry_of_lt (a i) (b j)
      (coordinatePresentationPolynomialEntry a b c hh i j) (lt_of_not_ge h)).symm

end MvPolynomial
