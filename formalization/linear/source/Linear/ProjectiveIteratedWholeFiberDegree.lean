module
public import Linear.ProjectivePullbackIteration
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Each ORIGINAL iterate has a newly constructed nonempty target open
where EVERY WHOLE point fiber has cardinality D^k, for the actual positive
degree D of the ORIGINAL function-field pullback. No q^r value, good
fiber, or fixed open across iterates is supplied. -/
theorem projective_iterates_general_whole_fiber_degree
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x0 hx0
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let L := FractionRing B
    let γ := projectiveChartFractionMap f V hq hf hV x0 hx0
    let D := Module.finrank γ.fieldRange L
    0 < D ∧ ∀ k : ℕ,
      ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
        (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
        ∀ (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet),
          MvPolynomial.eval y p ≠ 0 →
          ((f.iterate k).onPoints ⁻¹' {normalizedProjectivePoint y}).Finite ∧
            Nat.card ((f.iterate k).onPoints ⁻¹' {normalizedProjectivePoint y}) = D ^ k := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let L := FractionRing B
  let γ := projectiveChartFractionMap f V hq hf hV x0 hx0
  letI : Algebra.EssFiniteType B L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors B)
  letI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ B L
  letI : Module.Finite γ.fieldRange L := fieldEndomorphism_range_finite γ
  refine ⟨Module.finrank_pos, ?_⟩
  intro k
  obtain ⟨p, hp, hnonempty, hcard⟩ := projective_exists_general_whole_fiber_field_degree
    (f.iterate k) V (f.iterate_degree_pos hq k) (f.iterate_surjective hf k)
    (f.iterate_total_invariance V.zeroSet hV k) x0 hx0
  refine ⟨p, hp, hnonempty, ?_⟩
  intro y hy hyp
  obtain ⟨hfinite, hdim⟩ := hcard y hy hyp
  exact ⟨hfinite, hdim.trans
    (projectiveChartFractionMap_iterate_finrank f V hq hf hV x0 hx0 k)⟩

end LinearStudy
