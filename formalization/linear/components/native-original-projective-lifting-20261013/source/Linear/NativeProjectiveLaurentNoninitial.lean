module
public import Linear.NativeProjectiveLaurentFactors
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Inverting an actual base-linear chart frame also commutes with
the original open restriction. -/
theorem nativeIntegerTwistBaseSectionEquiv_symm_restrict {Y : Scheme.{u}}
    (π : (AlgebraicGeometry.Proj 𝓑) ⟶ Y) (a : S) (ha : a ∈ 𝓑 1) (k : ℤ)
    {U V : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ} (i : U ⟶ V)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (s : (Scheme.Modules.baseModulePresheaf π
      (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) k)).obj U) :
    (nativeIntegerTwistBaseSectionEquiv 𝓑 π a ha k V
      (fun p => hp (i.unop p))).symm
        ((Scheme.Modules.baseModulePresheaf π
          (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
            (nativeProjectiveRingIntegerPiece_graded 𝓑) k)).map i s) =
      (Scheme.Modules.baseModulePresheaf π
        (SheafOfModules.unit (AlgebraicGeometry.Proj 𝓑).ringCatSheaf)).map i
          ((nativeIntegerTwistBaseSectionEquiv 𝓑 π a ha k U hp).symm s) := by
  apply (nativeIntegerTwistBaseSectionEquiv 𝓑 π a ha k V
    (fun p => hp (i.unop p))).injective
  rw [LinearEquiv.apply_symm_apply]
  simpa only [LinearEquiv.apply_symm_apply] using
    nativeIntegerTwistBaseSectionEquiv_restrict 𝓑 π a ha k i hp
      ((nativeIntegerTwistBaseSectionEquiv 𝓑 π a ha k U hp).symm s)
end LinearStudy

namespace MvPolynomial
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {K : Type u} [Field K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A noninitial face preserves the actual coordinate frame, including
its inverse on sections of every integer twist. -/
theorem coordinateNativeIntegerTwistCechFactorFrame_symm_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : Fin (n + 1)) (k : ℤ)
    (s : Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n (a.delete j.succ).1) :
    (coordinateNativeIntegerTwistCechFactorFrame (K := K) a.1 k).symm
      ((Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) k)).map
          (coordinateOpenCechDelete (R := K) a j.succ).op s) =
    (Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
      (SheafOfModules.unit (Proj (homogeneousSubmodule σ K)).ringCatSheaf)).map
        (coordinateOpenCechDelete (R := K) a j.succ).op
          ((coordinateNativeIntegerTwistCechFactorFrame (K := K)
            (a.delete j.succ).1 k).symm s) := by
  exact LinearStudy.nativeIntegerTwistBaseSectionEquiv_symm_restrict
    (homogeneousSubmodule σ K) (homogeneousProjπ (R := K) (σ := σ))
    (X (a.1 0).down) (X_mem_homogeneousSubmodule_one K (a.1 0).down) k
    (coordinateOpenCechDelete (R := K) a j.succ).op
    (coordinateOpenCechIntersection_coordinate_notMem (K := K)
      (a.delete j.succ).1 0) s

/-- On ACTUAL native integer-twist factors, a noninitial Cech face is
the inclusion of the same global homogeneous Laurent weight. -/
theorem coordinateNativeIntegerTwistCechFactorLaurentEquiv_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : Fin (n + 1)) (k : ℤ)
    (s : Scheme.Modules.baseCechFactor (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ)) n (a.delete j.succ).1) :
    coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K) a.1 k
      ((Scheme.Modules.baseModulePresheaf (homogeneousProjπ (R := K) (σ := σ))
        (coordinateNativeIntegerTwist (K := K) (σ := σ) k)).map
          (coordinateOpenCechDelete (R := K) a j.succ).op s) =
      coordinateHomogeneousLaurentDeleteLinearMap (R := K) a j.succ k
        (coordinateNativeIntegerTwistCechFactorLaurentEquiv (K := K)
          (a.delete j.succ).1 k s) := by
  change coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
    (R := K) a.1 k
      ((coordinateNativeIntegerTwistCechFactorFrame (K := K) a.1 k).symm _) = _
  rw [coordinateNativeIntegerTwistCechFactorFrame_symm_delete_succ]
  exact coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_naturality_delete_succ
    (R := K) a j k _
end MvPolynomial
