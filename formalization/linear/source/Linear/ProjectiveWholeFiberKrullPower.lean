module
public import Linear.ProjectiveChartHilbertKrullDimension
public import Linear.ProjectiveWholeFiberHilbertPower
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Actual original chart function-field degree is q^r, with r identified
as the Krull dimension of the actual original affine chart coordinate ring. -/
theorem projective_chart_degree_krull_power
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x0 hx0
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let γ := projectiveChartFractionMap f V hq hf hV x0 hx0
    ∃ r : ℕ, r ≤ n ∧ ringKrullDim B = (r : WithBot ℕ∞) ∧
      Module.finrank γ.fieldRange (FractionRing B) = f.degree ^ r := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  obtain ⟨P, hP, hdeg, hD, hHilbert⟩ :=
    projectiveChartField_exists_hilbert_degree_power f V hq hf hV x0 hx0
  exact ⟨P.natDegree, hdeg,
    projective_chart_krull_dimension_of_hilbertPolynomial V x0 hx0 P hP hHilbert, hD⟩

/-- For EVERY original iterate, WHOLE general point fibers have (q^k)^r
points; the SAME r is the actual original chart's Krull dimension.
No geometric dimension, fiber-cardinality or degree formula is an input. -/
theorem projective_iterates_whole_fiber_krull_power
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      ∀ k : ℕ, ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
        (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
        ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
          MvPolynomial.eval y p ≠ 0 →
          ((f.iterate k).onPoints ⁻¹' {normalizedProjectivePoint y}).Finite ∧
            Nat.card ((f.iterate k).onPoints ⁻¹' {normalizedProjectivePoint y}) =
              (f.degree ^ k) ^ r := by
  obtain ⟨P, hP, hdeg, hHilbert, hiter⟩ :=
    projective_iterates_whole_fiber_hilbert_power f V hq hf hV x0 hx0
  exact ⟨P.natDegree, hdeg,
    projective_chart_krull_dimension_of_hilbertPolynomial V x0 hx0 P hP hHilbert, hiter⟩

end LinearStudy
