module
public import Linear.NativeCanonicalPolynomialEntryDuality
public import Linear.NativePolynomialPresentationWeights
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

/-- A selected ORIGINAL high weight has only a genuine integer-degree
sheaf transport. No condition is imposed on the other original weights. -/
def coordinateNativeHighIntegerWeightSheafIso (w : ℤ) (a : ℕ)
    (ha : w=(a:ℤ)+Fintype.card σ) :
    coordinateNativeIntegerTwist (K := K) (σ := σ) (-w) ≅
      coordinateNativeIntegerTwist (K := K) (σ := σ) (-(a:ℤ)-Fintype.card σ) :=
  eqToIso (congrArg (fun d => coordinateNativeIntegerTwist (K := K) (σ := σ) d)
    (show -w=-(a:ℤ)-Fintype.card σ by omega))

/-- The actual ORIGINAL high coefficient piece is its original natural
piece. The equality follows solely from the selected original weight. -/
def projectiveHighIntegerWeightPieceEquiv (w : ℤ) (a : ℕ)
    (ha : w=(a:ℤ)+Fintype.card σ) :
    LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K)
      (w-(Fintype.card σ:ℤ)) ≃ₗ[K] homogeneousSubmodule σ K a :=
  LinearEquiv.ofEq _ _ (by
    rw [ha]
    simp [LinearStudy.nativeProjectiveRingIntegerPiece])

/-- This transport preserves the ORIGINAL polynomial,not merely dimension. -/
theorem projectiveHighIntegerWeightPieceEquiv_apply (w : ℤ) (a : ℕ)
    (ha : w=(a:ℤ)+Fintype.card σ)
    (p : LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K)
      (w-(Fintype.card σ:ℤ))) :
    (projectiveHighIntegerWeightPieceEquiv w a ha p).1=p.1 := rfl

/-- The EXISTING all-integer single-free comparison actually factors
through these original high-weight transports and the canonical scalar
comparison. This proves the link;it is not a new comparison assumption. -/
theorem coordinateNativeIntegerWeightHomDualIso_high_factor
    (w : ℤ) (a : ℕ) (ha : w=(a:ℤ)+Fintype.card σ) (n : ℕ)
    (hcard : Fintype.card σ=n+2) :
    (coordinateNativeIntegerWeightHomDualIso (K := K) (σ := σ) w n hcard).hom =
    (ModuleCat.restrictScalars (coordinateCanonicalCoefficientRingEquiv K).toRingHom).map
      ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).map
        (coordinateNativeHighIntegerWeightSheafIso w a ha).hom) ≫
      (coordinateNativeCanonicalTopHomologyDualIso a n hcard).hom ≫
        (projectiveHighIntegerWeightPieceEquiv (K := K) w a ha).dualMap.toModuleIso.hom := by
  have hw : (Fintype.card σ:ℤ)≤w := by omega
  have hd : a=(w-(Fintype.card σ:ℤ)).toNat := by omega
  subst a
  rw [coordinateNativeIntegerWeightHomDualIso,dite_eq_left hw]
  simp only [coordinateNativeNonnegativeIntegerWeightHomDualIso,
    coordinateNativeCanonicalTopHomologyDualIso,coordinateNativeHighIntegerWeightSheafIso,
    projectiveHighIntegerWeightPieceEquiv,projectiveIntegerHomogeneousPieceNaturalEquiv,
    Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,Category.assoc]

end MvPolynomial
