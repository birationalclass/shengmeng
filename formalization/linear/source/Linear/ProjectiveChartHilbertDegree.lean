module
public import Linear.FieldEndomorphismConjugateDegree
public import Linear.ProjectiveRatioHilbertDegree
public import Linear.ProjectiveChartGenericMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem projectiveChartFractionMap_finrank_eq_ratio
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    Module.finrank (projectiveChartFractionMap f V hq hf hV x hx).fieldRange
      (FractionRing (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) =
        Module.finrank (projectiveCoordinateRatioMap f V hq hf hV x hx).fieldRange
          (projectiveCoordinateRatioField V) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let e := projectiveChartFractionRatioEquiv V x hx
  apply fieldEndomorphism_finrank_conjugate e
  intro z
  change e (e.symm (projectiveCoordinateRatioMap f V hq hf hV x hx (e z))) = _
  exact e.apply_symm_apply _

/-- The original chart field degree is calculated, not supplied:
q to the degree of the actual homogeneous-coordinate Hilbert polynomial. -/
theorem projectiveChartField_exists_hilbert_degree_power
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let γ := projectiveChartFractionMap f V hq hf hV x hx
    ∃ P : Polynomial ℚ, P ≠ 0 ∧ P.natDegree ≤ n ∧
      Module.finrank γ.fieldRange (FractionRing B) = f.degree ^ P.natDegree ∧
      ∃ K : ℕ, ∀ N > K,
        P.eval (N : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal N : ℚ) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  obtain ⟨P, hP, hdeg, hdegree, hK⟩ :=
    projectiveRatioField_exists_hilbert_degree_power f V hq hf hV x hx
  exact ⟨P, hP, hdeg,
    (projectiveChartFractionMap_finrank_eq_ratio f V hq hf hV x hx).trans hdegree, hK⟩

end LinearStudy
