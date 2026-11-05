module
public import Linear.ProjectiveLaurentAboveCanonicalBoundary
public import Linear.NativeProjectiveTwistCechVanishing
public import Linear.NativeProjectiveMatrixHomology
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

/-- The ACTUAL original Laurent ordered-Cech complex is exact in every
positive degree for EVERY original integer twist k>-card(sigma),including
intermediate negative twists. Original weightwise boundaries are proved. -/
theorem coordinateNativeLaurentOrderedCechComplex_exactAt_succ_of_gt_neg_card
    (k : ℤ) (hk : -(Fintype.card σ:ℤ)<k) (n : ℕ) :
    (coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) k).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n+1) ((n+1)+1) (by simp) (by simp)]
  have hsc : (ShortComplex.mk
      (coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ) k n)
      (coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ) k (n+1))
      (coordinateNativeLaurentOrderedCechDifferential_comp (K := K) (σ := σ) k n)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro s hs
    exact exists_preimage_coordinateHomogeneousLaurentOrderedCechDifferential_of_gt_neg_card
      (R := K) (σ := σ) k hk n s hs
  simpa only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',
    coordinateNativeLaurentOrderedCechComplex_X,coordinateNativeLaurentOrderedCechComplex_d] using hsc

/-- The actual native integer-twist sheaf has an exact actual ORIGINAL
ordered coordinate Cech complex above the canonical integer threshold.
No vanishing certificate or nonnegative-twist assumption is supplied. -/
theorem coordinateNativeIntegerTwist_orderedBaseCechComplex_exactAt_succ_of_gt_neg_card
    (k : ℤ) (hk : -(Fintype.card σ:ℤ)<k) (n : ℕ) :
    (Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ))).ExactAt (n+1) :=
  (coordinateNativeLaurentOrderedCechComplex_exactAt_succ_of_gt_neg_card (K := K) k hk n).of_iso
    (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ) k).symm

/-- EVERY positive actual native ordered-Cech homology object vanishes
for original k>-card(sigma). This is an actual IsZero theorem for the
original functor object,not yet derived SHEAF cohomology vanishing. -/
theorem coordinateNativeIntegerTwist_cechHomology_isZero_of_gt_neg_card
    (k : ℤ) (hk : -(Fintype.card σ:ℤ)<k) (n : ℕ) :
    IsZero ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)) :=
  (coordinateNativeIntegerTwist_orderedBaseCechComplex_exactAt_succ_of_gt_neg_card
    (K := K) k hk n).isZero_homology

/-- An ORIGINAL free integer weight w below N=card(sigma) has ZERO
positive native Cech homology. This supplies the previously missing free
terms for mixed original integer-weight presentations. -/
theorem coordinateNativeIntegerWeight_cechHomology_isZero_of_lt_card
    (w : ℤ) (hw : w<(Fintype.card σ:ℤ)) (n : ℕ) :
    IsZero ((coordinateNativeCechHomologyFunctor (K := K) (σ := σ) n).obj
      (coordinateNativeIntegerTwist (K := K) (σ := σ) (-w))) :=
  coordinateNativeIntegerTwist_cechHomology_isZero_of_gt_neg_card (-w) (by omega) n

end MvPolynomial
