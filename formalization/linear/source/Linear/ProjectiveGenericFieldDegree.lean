module
public import Linear.AwayPullbackFieldDegree
public import Linear.ProjectiveGeneralFiberRank
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The ORIGINAL chart generic rank is the degree of the actual
pullback image in the ORIGINAL function field; no degree value is input. -/
theorem projectiveChartOpenMap_finrank_eq_fieldRange
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x0 hx0
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let A := Localization.Away (projectiveChartDenominator f V)
    let γ := projectiveChartFractionMap f V hq hf hV x0 hx0
    let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
    letI : Algebra B A := φ.toRingHom.toAlgebra
    letI : SMul B A := φ.toRingHom.toAlgebra.toSMul
    letI : Module B A := Algebra.toModule
    Module.finrank B A = Module.finrank γ.fieldRange (FractionRing B) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  exact awayPullback_finrank_eq_fieldRange
    (projectiveChartDenominator f V)
    (projectiveChart_denominator_ne_zero f V hq hf hV x0 hx0)
    (projectiveChartFractionMap f V hq hf hV x0 hx0)
    (projectiveChartOpenMap f V hq hf hV x0 hx0)
    (projectiveChartOpenMap_fraction_comp f V hq hf hV x0 hx0)

/-- EVERY whole original point fiber on a constructed nonempty target
open has cardinality equal to the actual function-field degree. The
value q^r and a Scheme-fiber identification are not claimed. -/
theorem projective_exists_general_whole_fiber_field_degree
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x0 hx0
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let γ := projectiveChartFractionMap f V hq hf hV x0 hx0
    ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
      (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
      ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
        MvPolynomial.eval y p ≠ 0 →
        (f.onPoints ⁻¹' {normalizedProjectivePoint y}).Finite ∧
          Nat.card (f.onPoints ⁻¹' {normalizedProjectivePoint y}) =
            Module.finrank γ.fieldRange (FractionRing B) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
  letI : Algebra B A := φ.toRingHom.toAlgebra
  letI : SMul B A := φ.toRingHom.toAlgebra.toSMul
  letI : Module B A := Algebra.toModule
  obtain ⟨p, hp, hinhabited, hgood⟩ :=
    projective_exists_general_whole_fiber_generic_rank f V hq hf hV x0 hx0
  refine ⟨p, hp, hinhabited, ?_⟩
  intro y hy hyp
  obtain ⟨hfinite, _, hring⟩ := hgood y hy hyp
  dsimp only at hring
  exact ⟨hfinite, hring.2.2.trans
    (projectiveChartOpenMap_finrank_eq_fieldRange f V hq hf hV x0 hx0)⟩

end LinearStudy
