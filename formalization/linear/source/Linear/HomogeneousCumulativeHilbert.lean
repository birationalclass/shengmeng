module
public import Linear.HomogeneousCoordinateFiltration
public import Linear.GradedHilbertDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type*} [Field K] [Finite σ]

/-- The ACTUAL bounded-degree coordinate filtration has the cumulative Hilbert
series. Its relation to the original component series is derived. -/
theorem homogeneousQuotientFiltration_series_recurrence
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    (1 - PowerSeries.X) * gradedHilbertSeries (homogeneousQuotientFiltration I) =
      gradedHilbertSeries (homogeneousQuotientPiece I) := by
  classical
  have hX : (PowerSeries.X : PowerSeries ℤ) = PowerSeries.X ^ 1 := by simp
  rw [hX]
  apply PowerSeries.ext
  intro n
  rw [sub_mul, one_mul]
  simp only [map_sub, PowerSeries.coeff_X_pow_mul', gradedHilbertSeries, PowerSeries.coeff_mk,
    homogeneousQuotientFiltration_finrank I hI]
  change (↑(∑ m ∈ Finset.range (n + 1), homogeneousQuotientHilbert I m) : ℤ) -
      (if 1 ≤ n then ↑(∑ m ∈ Finset.range (n - 1 + 1), homogeneousQuotientHilbert I m) else 0) =
        ↑(homogeneousQuotientHilbert I n)
  cases n with
  | zero => simp
  | succ n =>
      simp only [Nat.le_add_left, ite_true, Nat.add_sub_cancel]
      rw [Finset.sum_range_succ (fun m => homogeneousQuotientHilbert I m) (n + 1)]
      push_cast
      omega

/-- Hilbert--Serre gives a numerator for the ACTUAL coordinate filtration by
one more factor of (1-X), not an assumed filtered growth polynomial. -/
theorem homogeneousQuotientFiltration_series_rational
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    ∃ p : Polynomial ℤ,
      (1 - PowerSeries.X) ^ (Nat.card σ + 1) *
        gradedHilbertSeries (homogeneousQuotientFiltration I) = (p : PowerSeries ℤ) := by
  obtain ⟨p, hp⟩ := homogeneousQuotientHilbertSeries_rational I hI
  refine ⟨p, ?_⟩
  calc
    (1 - PowerSeries.X) ^ (Nat.card σ + 1) *
        gradedHilbertSeries (homogeneousQuotientFiltration I) =
      (1 - PowerSeries.X) ^ Nat.card σ *
        ((1 - PowerSeries.X) * gradedHilbertSeries (homogeneousQuotientFiltration I)) := by ring
    _ = (1 - PowerSeries.X) ^ Nat.card σ *
        gradedHilbertSeries (homogeneousQuotientPiece I) := by
      rw [homogeneousQuotientFiltration_series_recurrence I hI]
    _ = (p : PowerSeries ℤ) := hp

theorem homogeneousQuotientCumulativeHilbertPolynomial_existsUnique
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    ∃! P : Polynomial ℚ, ∃ N : ℕ, ∀ n > N,
      P.eval (n : ℚ) = (Module.finrank K (homogeneousQuotientFiltration I n) : ℚ) :=
  gradedHilbertPolynomial_existsUnique (homogeneousQuotientFiltration I) (Nat.card σ + 1)
    (homogeneousQuotientFiltration_series_rational I hI)

/-- Identify a genuinely proved rational series with mathlib's Hilbert
polynomial. This is used with actual coordinate Hilbert series below. -/
theorem hilbertPolynomial_eq_of_rational_series (H : PowerSeries ℚ)
    (p : Polynomial ℚ) (d : ℕ)
    (h : (1 - PowerSeries.X) ^ d * H = (p : PowerSeries ℚ))
    (P : Polynomial ℚ) (hP : ∃ N : ℕ, ∀ n > N, P.eval (n : ℚ) = PowerSeries.coeff n H) :
    P = Polynomial.hilbertPoly p d := by
  have hH : H = (p : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ d).val := by
    calc
      H = (PowerSeries.invOneSubPow ℚ d).val * ((1 - PowerSeries.X) ^ d * H) := by
        rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow, ← mul_assoc, Units.val_inv, one_mul]
      _ = (PowerSeries.invOneSubPow ℚ d).val * (p : PowerSeries ℚ) := by rw [h]
      _ = (p : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ d).val := mul_comm _ _
  obtain ⟨N, hN⟩ := hP
  exact Polynomial.eq_hilbertPoly_of_forall_coeff_eq_eval N (fun n hn => by
    rw [← hH, hN n hn])

/-- The same nonzero Hilbert numerator increases the eventual polynomial
degree by one when its denominator receives one extra factor (1-X). -/
theorem hilbertPoly_natDegree_succ (p : Polynomial ℚ) (d : ℕ)
    (hP : Polynomial.hilbertPoly p d ≠ 0) :
    (Polynomial.hilbertPoly p (d + 1)).natDegree =
      (Polynomial.hilbertPoly p d).natDegree + 1 := by
  have hp : p ≠ 0 := by
    intro hp
    subst p
    exact hP (Polynomial.hilbertPoly_zero_left d)
  have hroot : p.rootMultiplicity 1 < d := by
    by_contra h
    exact hP (Polynomial.hilbertPoly_eq_zero_of_le_rootMultiplicity_one (not_lt.mp h))
  rw [Polynomial.natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt hp
      (show p.rootMultiplicity 1 < d + 1 by omega),
    Polynomial.natDegree_hilbertPoly_of_ne_zero hP]
  omega

end LinearStudy
