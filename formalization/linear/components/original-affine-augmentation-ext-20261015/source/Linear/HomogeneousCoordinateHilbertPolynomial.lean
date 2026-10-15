module
public import Linear.HomogeneousCoordinateHilbertSeries
public import Mathlib.RingTheory.Polynomial.HilbertPoly
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Use mathlib's existing rational-series Hilbert polynomial backend.
The input is a proved generating-series identity, not an eventual growth polynomial. -/
theorem gradedHilbertPolynomial_existsUnique (ℳ : ℕ → Submodule K M) (d : ℕ)
    (h : ∃ p : Polynomial ℤ,
      (1 - PowerSeries.X) ^ d * gradedHilbertSeries ℳ = (p : PowerSeries ℤ)) :
    ∃! P : Polynomial ℚ, ∃ N : ℕ, ∀ n > N,
      P.eval (n : ℚ) = (Module.finrank K (ℳ n) : ℚ) := by
  obtain ⟨p, hp⟩ := h
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  let H := PowerSeries.map φ (gradedHilbertSeries ℳ)
  let pQ := Polynomial.map φ p
  have hQ : (1 - PowerSeries.X) ^ d * H = (pQ : PowerSeries ℚ) := by
    simpa [H, pQ] using
      congrArg (PowerSeries.map φ) hp
  have hH : H = (pQ : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ d).val := by
    calc
      H = (PowerSeries.invOneSubPow ℚ d).val *
          ((1 - PowerSeries.X) ^ d * H) := by
        rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow, ← mul_assoc,
          Units.val_inv, one_mul]
      _ = (PowerSeries.invOneSubPow ℚ d).val * (pQ : PowerSeries ℚ) := by rw [hQ]
      _ = (pQ : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ d).val := mul_comm _ _
  have hcoeff (n : ℕ) : PowerSeries.coeff n H = (Module.finrank K (ℳ n) : ℚ) := by
    simp [H, φ, gradedHilbertSeries, PowerSeries.coeff_map]
  obtain ⟨P, ⟨N, hN⟩, huniq⟩ := Polynomial.existsUnique_hilbertPoly pQ d
  refine ⟨P, ⟨N, fun n hn => ?_⟩, ?_⟩
  · exact (hN n hn).symm.trans (by rw [← hH]; exact hcoeff n)
  · rintro F ⟨N', hN'⟩
    apply huniq F
    refine ⟨N', fun n hn => ?_⟩
    rw [← hH, hcoeff n, ← hN' n hn]

/-- The ORIGINAL quotient Hilbert function agrees eventually with a UNIQUE rational
polynomial, derived from I and its actual finite homogeneous pieces. No geometric
dimension or equality between function-field degree and q^dim(V) is assumed here. -/
theorem homogeneousQuotientHilbertPolynomial_existsUnique
    {σ : Type*} [Finite σ] (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    ∃! P : Polynomial ℚ, ∃ N : ℕ, ∀ n > N,
      P.eval (n : ℚ) = (homogeneousQuotientHilbert I n : ℚ) :=
  gradedHilbertPolynomial_existsUnique (homogeneousQuotientPiece I) (Nat.card σ)
    (homogeneousQuotientHilbertSeries_rational I hI)

end LinearStudy
