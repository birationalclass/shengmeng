module
public import Linear.NativeIntegerFreeTwistRegrading
public import Linear.NativeIntegerFreeFamilyHomDuality
public import Linear.IntegerShiftedFreeDualRegrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable {J : Type} [Fintype J] [DecidableEq J]

/-- Construct the comparison for the ORIGINAL native free E_w(k),for
EVERY original integer k,w. Actual weight-regrading sheaf iso,existing
all-integer free comparison and genuine original polynomial transport
are used. No free-twist comparison is a supplied premise. -/
def coordinateNativeIntegerTwistedFreeFamilyCoefficientDualIso
    (w : J → ℤ) (k : ℤ) (n : ℕ) (hcard : Fintype.card σ=n+2) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
        (LinearStudy.nativeProjectiveModuleSheaf (homogeneousSubmodule σ K)
          (LinearStudy.integerShiftedFreePiece (homogeneousSubmodule σ K) w)
          (LinearStudy.integerShiftedFreePiece_smul_homogeneous (homogeneousSubmodule σ K) w) k)) ≅
    ModuleCat.of K (Module.Dual K
      (LinearStudy.integerShiftedFreeDualCoordinatePiece (homogeneousSubmodule σ K)
        w (-(Fintype.card σ:ℤ)-k))) := by
  let B := homogeneousSubmodule σ K
  let G := (coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n) ⋙
    ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let ι := LinearStudy.nativeIntegerFreeTwistRegradingIso B w k
  let ε := (LinearStudy.integerShiftedFreeDualCoordinateRegradingEquiv B w k
    (-(Fintype.card σ:ℤ))).dualMap.toModuleIso
  exact (G.mapIso ι).symm.trans
    ((coordinateNativeIntegerFreeFamilyCoefficientDualIso (fun j => w j-k) n hcard).trans ε.symm)

end MvPolynomial
