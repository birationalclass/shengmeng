module
public import Linear.HomogeneousCoordinateHilbertPositive
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- A proved Hilbert--Serre identity bounds the degree of an actual eventual
Hilbert polynomial. It does not identify that degree with Krull dimension. -/
theorem gradedHilbertPolynomial_natDegree_le (ℳ : ℕ → Submodule K M) (d : ℕ)
    (h : ∃ p : Polynomial ℤ,
      (1 - PowerSeries.X) ^ d * gradedHilbertSeries ℳ = (p : PowerSeries ℤ))
    (P : Polynomial ℚ) (hP : P ≠ 0)
    (hN : ∃ N : ℕ, ∀ n > N,
      P.eval (n : ℚ) = (Module.finrank K (ℳ n) : ℚ)) :
    P.natDegree ≤ d - 1 := by
  obtain ⟨p, hp⟩ := h
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  let H := PowerSeries.map φ (gradedHilbertSeries ℳ)
  let pQ := Polynomial.map φ p
  have hQ : (1 - PowerSeries.X) ^ d * H = (pQ : PowerSeries ℚ) := by
    simpa [H, pQ] using congrArg (PowerSeries.map φ) hp
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
  obtain ⟨N, hN⟩ := hN
  have heq : P = Polynomial.hilbertPoly pQ d :=
    Polynomial.eq_hilbertPoly_of_forall_coeff_eq_eval N (fun n hn => by
      rw [← hH, hcoeff n, hN n hn])
  have hh : Polynomial.hilbertPoly pQ d ≠ 0 := heq ▸ hP
  rw [heq, Polynomial.natDegree_hilbertPoly_of_ne_zero hh]
  omega

/-- Derive a NONZERO Hilbert polynomial of the original projective coordinate
ring, with degree bounded by the ambient projective dimension. -/
theorem projective_coordinate_hilbertPolynomial_degree_bound {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    ∃ P : Polynomial ℚ, P ≠ 0 ∧ P.natDegree ≤ n ∧ ∃ N : ℕ, ∀ m > N,
      P.eval (m : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal m : ℚ) ∧
        0 < P.eval (m : ℚ) := by
  obtain ⟨P, hp, N, hN⟩ := projective_coordinate_hilbertPolynomial_nonzero V
  refine ⟨P, hp, ?_, N, hN⟩
  have hseries : ∃ p : Polynomial ℤ,
      (1 - PowerSeries.X) ^ (n + 1) *
        gradedHilbertSeries (homogeneousQuotientPiece V.ideal.toIdeal) =
          (p : PowerSeries ℤ) := by
    simpa using (homogeneousQuotientHilbertSeries_rational
      V.ideal.toIdeal V.ideal.isHomogeneous)
  have h := gradedHilbertPolynomial_natDegree_le (homogeneousQuotientPiece V.ideal.toIdeal)
    (n + 1) hseries P hp ⟨N, fun m hm => (hN m hm).1⟩
  simpa using h

end LinearStudy
