module
public import Linear.ProjectiveConeDegreeFactor
public import Linear.ProjectiveConeFieldGrowthDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The whole original PROJECTIVE image degree is q to the actual
Hilbert-polynomial degree. Geometric dimension comparison is not asserted. -/
theorem projectiveRatioField_exists_hilbert_degree_power
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    let E := projectiveCoordinateRatioField V
    let σ := projectiveCoordinateRatioMap f V hq hf hV x hx
    ∃ P : Polynomial ℚ, P ≠ 0 ∧ P.natDegree ≤ n ∧
      Module.finrank σ.fieldRange E = f.degree ^ P.natDegree ∧
      ∃ K : ℕ, ∀ N > K,
        P.eval (N : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal N : ℚ) := by
  letI := V.prime
  obtain ⟨P, C, hP, hC, hdeg, hCdeg, hcone, K, hK⟩ :=
    projectiveConeFractionField_exists_hilbert_degree_power f V hq hf hV
  have hfactor := projectiveConeFractionField_degree_factor f V hq hf hV x hx
  dsimp only at hfactor
  rw [hcone, hCdeg, pow_succ'] at hfactor
  have hproj : Module.finrank (projectiveCoordinateRatioMap f V hq hf hV x hx).fieldRange
      (projectiveCoordinateRatioField V) = f.degree ^ P.natDegree := by
    exact (Nat.eq_of_mul_eq_mul_left hq hfactor).symm
  exact ⟨P, hP, hdeg, hproj, K, fun N hN => (hK N hN).1⟩

end LinearStudy
