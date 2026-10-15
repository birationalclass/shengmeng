module
public import Linear.HomogeneousCumulativeHilbert
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type*} [Field K] [Finite σ]

/-- For the ORIGINAL coordinate quotient, the cumulative Hilbert polynomial
has degree one greater than its nonzero component Hilbert polynomial. Both
polynomials are obtained from the actual graded pieces, not supplied growth data. -/
theorem homogeneousQuotientCumulativeHilbertPolynomial_degree
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (P : Polynomial ℚ) (hP : P ≠ 0)
    (hN : ∃ N : ℕ, ∀ n > N,
      P.eval (n : ℚ) = (homogeneousQuotientHilbert I n : ℚ)) :
    ∃ C : Polynomial ℚ, C ≠ 0 ∧ C.natDegree = P.natDegree + 1 ∧
      ∃ N : ℕ, ∀ n > N,
        C.eval (n : ℚ) = (Module.finrank K (homogeneousQuotientFiltration I n) : ℚ) := by
  obtain ⟨p, hp⟩ := homogeneousQuotientHilbertSeries_rational I hI
  obtain ⟨C, hC, _⟩ := homogeneousQuotientCumulativeHilbertPolynomial_existsUnique I hI
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  let H := PowerSeries.map φ (gradedHilbertSeries (homogeneousQuotientPiece I))
  let G := PowerSeries.map φ (gradedHilbertSeries (homogeneousQuotientFiltration I))
  let pQ := Polynomial.map φ p
  have hH : (1 - PowerSeries.X) ^ Nat.card σ * H = (pQ : PowerSeries ℚ) := by
    simpa [H, pQ] using congrArg (PowerSeries.map φ) hp
  have hrec : (1 - PowerSeries.X) * G = H := by
    simpa [G, H] using congrArg (PowerSeries.map φ)
      (homogeneousQuotientFiltration_series_recurrence I hI)
  have hG : (1 - PowerSeries.X) ^ (Nat.card σ + 1) * G = (pQ : PowerSeries ℚ) := by
    calc
      (1 - PowerSeries.X) ^ (Nat.card σ + 1) * G =
        (1 - PowerSeries.X) ^ Nat.card σ * ((1 - PowerSeries.X) * G) := by ring
      _ = (1 - PowerSeries.X) ^ Nat.card σ * H := by rw [hrec]
      _ = (pQ : PowerSeries ℚ) := hH
  have hcoeff (n : ℕ) : PowerSeries.coeff n H = (homogeneousQuotientHilbert I n : ℚ) := by
    simp [H, φ, gradedHilbertSeries, PowerSeries.coeff_map, homogeneousQuotientHilbert]
  have gcoeff (n : ℕ) : PowerSeries.coeff n G =
      (Module.finrank K (homogeneousQuotientFiltration I n) : ℚ) := by
    simp [G, φ, gradedHilbertSeries, PowerSeries.coeff_map]
  have heP : P = Polynomial.hilbertPoly pQ (Nat.card σ) := by
    apply hilbertPolynomial_eq_of_rational_series H pQ (Nat.card σ) hH
    obtain ⟨N, hN⟩ := hN
    exact ⟨N, fun n hn => by rw [hcoeff n, hN n hn]⟩
  have heC : C = Polynomial.hilbertPoly pQ (Nat.card σ + 1) := by
    apply hilbertPolynomial_eq_of_rational_series G pQ (Nat.card σ + 1) hG
    obtain ⟨N, hC⟩ := hC
    exact ⟨N, fun n hn => by rw [gcoeff n, hC n hn]⟩
  have hdegree : C.natDegree = P.natDegree + 1 := by
    rw [heC, heP]
    exact hilbertPoly_natDegree_succ pQ (Nat.card σ) (heP ▸ hP)
  refine ⟨C, ?_, hdegree, hC⟩
  intro hzero
  simp only [hzero, Polynomial.natDegree_zero] at hdegree
  omega

/-- Actual bounded-degree polynomial functions on the ORIGINAL nonempty
integral projective variety have a nonzero eventual polynomial of degree one
greater than the actual homogeneous Hilbert polynomial. The identification
of this degree with geometric dimension is not assumed or asserted here. -/
theorem projective_coordinate_hilbertPolynomial_growth {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    ∃ P C : Polynomial ℚ, P ≠ 0 ∧ C ≠ 0 ∧ P.natDegree ≤ n ∧
      C.natDegree = P.natDegree + 1 ∧ ∃ N : ℕ, ∀ m > N,
        P.eval (m : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal m : ℚ) ∧
        C.eval (m : ℚ) =
          (Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal m) : ℚ) := by
  obtain ⟨P, hP, hdeg, NP, hNP⟩ := projective_coordinate_hilbertPolynomial_degree_bound V
  obtain ⟨C, hC, hCdeg, NC, hNC⟩ :=
    homogeneousQuotientCumulativeHilbertPolynomial_degree V.ideal.toIdeal V.ideal.isHomogeneous
      P hP ⟨NP, fun m hm => (hNP m hm).1⟩
  exact ⟨P, C, hP, hC, hdeg, hCdeg, max NP NC,
    fun m hm => ⟨(hNP m (lt_of_le_of_lt (le_max_left _ _) hm)).1,
      hNC m (lt_of_le_of_lt (le_max_right _ _) hm)⟩⟩

end LinearStudy
