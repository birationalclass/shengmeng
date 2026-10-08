module
public import Linear.NormalizationDifferentialRank
public import Linear.ProjectiveChartHilbertKrullDimension
public import Linear.ProjectiveSmoothPointParameters
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- For the actual original inhabited projective chart, its differential rank
equals its actual Krull dimension; singular points are allowed on the variety. -/
theorem IntegralProjectiveEquations.chart_krull_dimension_eq_differential_rank
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) =
      (Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) : WithBot ℕ∞) := by
  letI := V.affineIdeal_isPrime_of_point x hx
  exact finiteType_domain_krull_dimension_eq_differential_finrank ℂ
    (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)

/-- The original homogeneous Hilbert degree and the actual chart's differential
rank used by the local parameter constructions are the SAME integer. -/
theorem projective_chart_differential_rank_of_hilbertPolynomial
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (P : Polynomial ℚ) (hP : P ≠ 0)
    (hHilbert : ∃ N : ℕ, ∀ m > N,
      P.eval (m : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal m : ℚ)) :
    Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
      (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) = P.natDegree := by
  have h := (V.chart_krull_dimension_eq_differential_rank x hx).symm.trans
    (projective_chart_krull_dimension_of_hilbertPolynomial V x hx P hP hHilbert)
  exact_mod_cast h

/-- Actual polynomial local parameters at an original smooth point, with their
number identified as the SAME original Hilbert degree, rather than an arbitrary
local model dimension. -/
theorem IntegralProjectiveEquations.smoothPoint_hilbert_dimension_parameters
    (V : IntegralProjectiveEquations n) (hproper : V.ideal.toIdeal ≠ ⊥)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hs : Algebra.IsSmoothAt ℂ (V.affinePoint y hy).asIdeal)
    (P : Polynomial ℚ) (hP : P ≠ 0)
    (hHilbert : ∃ N : ℕ, ∀ m > N,
      P.eval (m : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal m : ℚ)) :
    let Q := (V.affinePoint y hy).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)
    let J := V.affineIdeal.map (algebraMap _ (Localization.AtPrime Q))
    ∃ a : Fin P.natDegree → MvPolynomial (Fin n) ℂ,
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk J
        (algebraMap _ (Localization.AtPrime Q) (a i)))) =
          (Q.map (algebraMap _ (Localization.AtPrime Q))).map (Ideal.Quotient.mk J) := by
  intro Q J
  obtain ⟨r, a, hr, ha⟩ := V.smoothPoint_polynomial_parameters hproper y hy hs
  have hrP : r = P.natDegree := hr.trans
    (projective_chart_differential_rank_of_hilbertPolynomial V y hy P hP hHilbert)
  clear hr
  subst r
  exact ⟨a, ha⟩

end LinearStudy
