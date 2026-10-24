module
public import Linear.QuotientHilbertKrullDimension
public import Linear.ProjectiveCoordinateHilbertGrowth
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The cone's dimension formula for any actual nonzero eventual component
Hilbert polynomial; this does not require choosing a fresh polynomial. -/
theorem projective_cone_krull_dimension_of_hilbertPolynomial {n : ℕ}
    (V : IntegralProjectiveEquations n) (P : Polynomial ℚ) (hP : P ≠ 0)
    (hHilbert : ∃ N : ℕ, ∀ m > N,
      P.eval (m : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal m : ℚ)) :
    ringKrullDim (CoordinateRing n ⧸ V.ideal.toIdeal) =
      ((P.natDegree + 1 : ℕ) : WithBot ℕ∞) := by
  letI : V.ideal.toIdeal.IsPrime := V.prime
  obtain ⟨C, hC, hCdeg, hN⟩ := homogeneousQuotientCumulativeHilbertPolynomial_degree
    V.ideal.toIdeal V.ideal.isHomogeneous P hP hHilbert
  have hdim := quotient_cumulative_hilbert_degree_eq_ringKrullDim
    V.ideal.toIdeal C hC hN
  simpa only [hCdeg] using hdim

/-- The ACTUAL original projective cone coordinate ring has Krull dimension
one greater than its ACTUAL homogeneous Hilbert polynomial degree. -/
theorem projective_cone_hilbertPolynomial_krull_dimension {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    ∃ P : Polynomial ℚ, P ≠ 0 ∧ P.natDegree ≤ n ∧
      ringKrullDim (CoordinateRing n ⧸ V.ideal.toIdeal) =
        ((P.natDegree + 1 : ℕ) : WithBot ℕ∞) ∧
      ∃ N : ℕ, ∀ m > N,
        P.eval (m : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal m : ℚ) := by
  letI : V.ideal.toIdeal.IsPrime := V.prime
  obtain ⟨P, C, hP, hC, hdeg, hCdeg, N, hN⟩ :=
    projective_coordinate_hilbertPolynomial_growth V
  have hdim := quotient_cumulative_hilbert_degree_eq_ringKrullDim
    V.ideal.toIdeal C hC ⟨N, fun m hm => (hN m hm).2⟩
  refine ⟨P, hP, hdeg, ?_, N, fun m hm => (hN m hm).1⟩
  simpa only [hCdeg] using hdim

end LinearStudy
