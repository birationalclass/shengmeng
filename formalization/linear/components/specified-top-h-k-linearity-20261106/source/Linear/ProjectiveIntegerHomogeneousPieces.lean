module
public import Linear.NativeProjectiveRingIntegerPieces
public import Linear.NativePolynomialTopDualityNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open CategoryTheory CategoryTheory.Limits
variable {K : Type} [Field K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ACTUAL original nonnegative INTEGER polynomial piece is its
original natural-degree piece. This is genuine equality transport. -/
def projectiveIntegerHomogeneousPieceNaturalEquiv (d : ℤ) (hd : 0≤d) :
    LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K) d ≃ₗ[K]
      homogeneousSubmodule σ K d.toNat :=
  LinearEquiv.ofEq _ _ (by simp [LinearStudy.nativeProjectiveRingIntegerPiece,hd])

/-- The actual original polynomial is unchanged by integer-degree transport. -/
theorem projectiveIntegerHomogeneousPieceNaturalEquiv_apply (d : ℤ) (hd : 0≤d)
    (p : LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K) d) :
    (projectiveIntegerHomogeneousPieceNaturalEquiv d hd p).1 = p.1 := rfl

/-- The actual K-dual of an ORIGINAL negative integer degree piece is
ZERO,by its proved actual bottom-submodule definition and mathlib's
linear-map Unique-on-zero-domain instance. No dimension hypothesis. -/
theorem projectiveIntegerHomogeneousDual_isZero_of_neg (d : ℤ) (hd : d<0) :
    IsZero (ModuleCat.of K (Module.Dual K
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K) d))) := by
  unfold LinearStudy.nativeProjectiveRingIntegerPiece
  rw [if_neg (not_le_of_gt hd)]
  exact ModuleCat.isZero_of_subsingleton _

end MvPolynomial
