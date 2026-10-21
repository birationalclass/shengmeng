module
public import Linear.ProjectiveIntegerHomogeneousPieces
public import Linear.NativeProjectiveAboveCanonicalCechVanishing
public import Linear.ProjectiveDualCoefficientRestriction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
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

/-- ORIGINAL weights w>=N give the actual free top Cech/degree-piece
duality by proved arithmetic casts,original natural top Cech duality,
actual canonical K/Gamma scalar restriction,and original integer pieces. -/
def coordinateNativeNonnegativeIntegerWeightHomDualIso
    (w : ℤ) (hw : (Fintype.card σ:ℤ)≤w) (n : ℕ) (hcard : Fintype.card σ=n+2) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (-w))) ≅
    ModuleCat.of K (Module.Dual K
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K)
        (w-(Fintype.card σ:ℤ)))) := by
  let d := w-(Fintype.card σ:ℤ)
  have hd : 0≤d := by dsimp [d]; omega
  have ht : -w = -(d.toNat:ℤ)-(Fintype.card σ:ℤ) := by dsimp [d]; omega
  let F := ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom
  let H := coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n
  exact (F.mapIso (H.mapIso (eqToIso (congrArg
    (fun k => coordinateNativeIntegerTwist (K := K) (σ := σ) k) ht)))).trans
    ((F.mapIso (coordinateNativeGeneralTopHomologyDualIso (K := K) (σ := σ) d.toNat n hcard)).trans
      ((coordinateCanonicalHomogeneousDualCoefficientIso (σ := σ) K d.toNat).symm.trans
        (projectiveIntegerHomogeneousPieceNaturalEquiv (K := K) (σ := σ) d hd).dualMap.toModuleIso))

/-- ORIGINAL weights w<N have actual ZERO original Cech homology and
actual ZERO original homogeneous coefficient dual. Mathlib's zero-object
iso constructs their comparison;neither vanishing is supplied as input. -/
def coordinateNativeBelowCanonicalIntegerWeightHomDualIso
    (w : ℤ) (hw : w<(Fintype.card σ:ℤ)) (n : ℕ) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (-w))) ≅
    ModuleCat.of K (Module.Dual K
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K)
        (w-(Fintype.card σ:ℤ)))) :=
  (Functor.map_isZero
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom)
    (coordinateNativeIntegerWeight_cechHomology_isZero_of_lt_card (K := K) w hw n)).iso
      (projectiveIntegerHomogeneousDual_isZero_of_neg (K := K) (σ := σ)
        (w-(Fintype.card σ:ℤ)) (by omega))

/-- For EVERY ORIGINAL INTEGER weight w,the ACTUAL native free twist
has original top ordered-Cech homology equal to the K-dual of the ORIGINAL
integer homogeneous piece S_(w-N). Handles both sides of the canonical
threshold,using proved original objects,arithmetic and actual zero cases.
This is the single-free-term case;whole mixed presentation remains separate. -/
def coordinateNativeIntegerWeightHomDualIso (w : ℤ) (n : ℕ) (hcard : Fintype.card σ=n+2) :
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).obj
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
        (coordinateNativeIntegerTwist (K := K) (σ := σ) (-w))) ≅
    ModuleCat.of K (Module.Dual K
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K)
        (w-(Fintype.card σ:ℤ)))) :=
  if h : (Fintype.card σ:ℤ)≤w then
    coordinateNativeNonnegativeIntegerWeightHomDualIso w h n hcard
  else coordinateNativeBelowCanonicalIntegerWeightHomDualIso w (lt_of_not_ge h) n

end MvPolynomial
