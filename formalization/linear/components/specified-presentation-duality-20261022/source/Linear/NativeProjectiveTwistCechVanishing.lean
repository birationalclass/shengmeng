module
public import Linear.NativeProjectiveLaurentComplex
public import Linear.ProjectiveLaurentPositiveBoundary
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The explicit Laurent-weight complex is exact in every positive
degree for every nonnegative twist, by finite weightwise contraction. -/
theorem coordinateNativeLaurentOrderedCechComplex_exactAt_succ
    (j : σ) (k : ℤ) (hk : 0 ≤ k) (n : ℕ) :
    (coordinateNativeLaurentOrderedCechComplex (K := K) (σ := σ) k).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n+1) ((n+1)+1) (by simp) (by simp)]
  have hsc : (ShortComplex.mk
      (coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ) k n)
      (coordinateHomogeneousLaurentOrderedCechDifferential (R := K) (σ := σ) k (n+1))
      (coordinateNativeLaurentOrderedCechDifferential_comp (K := K) (σ := σ) k n)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro s hs
    exact exists_preimage_coordinateHomogeneousLaurentOrderedCechDifferential
      (R := K) (σ := σ) j k hk n s hs
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    coordinateNativeLaurentOrderedCechComplex_X, coordinateNativeLaurentOrderedCechComplex_d] using hsc

/-- The ACTUAL native integer-twist sheaf on the original projective
scheme has an exact actual ordered Cech complex in every positive
degree whenever its twist is nonnegative. No vanishing certificate is assumed. -/
theorem coordinateNativeIntegerTwist_orderedBaseCechComplex_exactAt_succ
    (j : σ) (k : ℤ) (hk : 0 ≤ k) (n : ℕ) :
    (Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := σ))
      (coordinateNativeIntegerTwist (K := K) (σ := σ) k)
      (coordinateOpenCover (R := K) (σ := σ))).ExactAt (n+1) :=
  (coordinateNativeLaurentOrderedCechComplex_exactAt_succ (K := K) j k hk n).of_iso
    (coordinateNativeLaurentOrderedCechComplexIso (K := K) (σ := σ) k).symm

/-- On P^r over K, every actual native nonnegative twist has an exact
ordered coordinate Cech complex in every positive degree, with no
extra nonemptiness or coordinate-choice hypothesis. -/
theorem coordinateNativeProjectiveSpaceTwist_exactAt_succ
    (r : ℕ) (k : ℤ) (hk : 0 ≤ k) (n : ℕ) :
    (Scheme.Modules.orderedBaseCechComplex (homogeneousProjπ (R := K) (σ := Fin (r+1)))
      (coordinateNativeIntegerTwist (K := K) (σ := Fin (r+1)) k)
      (coordinateOpenCover (R := K) (σ := Fin (r+1)))).ExactAt (n+1) :=
  coordinateNativeIntegerTwist_orderedBaseCechComplex_exactAt_succ (K := K)
    (0 : Fin (r+1)) k hk n
end MvPolynomial
