module
public import Linear.FractionPullbackFieldDegree
public import Linear.ProjectiveGenericGrowthDegree
public import Linear.ProjectiveCoordinateFractionMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The ORIGINAL cone pullback generic rank is its actual fraction-field
image degree. This is not the projective degree-zero field. -/
theorem projectiveCoordinateDomainMap_finrank_eq_fieldRange
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    letI := V.prime
    let A := CoordinateRing n ⧸ V.ideal.toIdeal
    let γ := projectiveCoordinateFractionMap f V hq hf hV
    let φ := projectiveCoordinateDomainMap f V hq hf hV
    letI : Algebra A A := φ.toRingHom.toAlgebra
    letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
    letI : Module A A := Algebra.toModule
    Module.finrank A A = Module.finrank γ.fieldRange (FractionRing A) := by
  letI := V.prime
  apply fractionPullback_finrank_eq_fieldRange
    (projectiveCoordinateFractionMap f V hq hf hV)
    (projectiveCoordinateDomainMap f V hq hf hV)
  apply AlgHom.ext
  intro a
  exact (projectiveCoordinateFractionMap_algebraMap f V hq hf hV a).symm

/-- From only the original f,V, derive both actual Hilbert polynomials
and the q-power formula for the ORIGINAL cone fraction-field degree. -/
theorem projectiveConeFractionField_exists_hilbert_degree_power
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    letI := V.prime
    let A := CoordinateRing n ⧸ V.ideal.toIdeal
    let γ := projectiveCoordinateFractionMap f V hq hf hV
    ∃ P C : Polynomial ℚ, P ≠ 0 ∧ C ≠ 0 ∧ P.natDegree ≤ n ∧
      C.natDegree = P.natDegree + 1 ∧
      Module.finrank γ.fieldRange (FractionRing A) = f.degree ^ C.natDegree ∧
      ∃ K : ℕ, ∀ N > K,
        P.eval (N : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal N : ℚ) ∧
        C.eval (N : ℚ) =
          (Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal N) : ℚ) := by
  letI := V.prime
  obtain ⟨P, C, hP, hC, hdeg, hCdeg, hrank, K, hK⟩ :=
    projectiveCoordinateDomainMap_exists_hilbert_rank_power f V hq hf hV
  refine ⟨P, C, hP, hC, hdeg, hCdeg, ?_, K, hK⟩
  exact (projectiveCoordinateDomainMap_finrank_eq_fieldRange f V hq hf hV).symm.trans hrank

end LinearStudy
