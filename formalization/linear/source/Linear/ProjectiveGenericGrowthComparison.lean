module
public import Linear.ProjectiveFilteredUpperBound
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Two-sided growth estimates for the ORIGINAL finite cone pullback.
The rank, homogeneous family, shifts and common denominator are all
derived from the original map and ideal. No growth estimate is input.
Turning these inequalities into the precise degree formula remains a
separate polynomial-growth obligation. -/
theorem projectiveCoordinateDomainMap_generic_growth_comparison
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    let A := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveCoordinateDomainMap f V hq hf hV
    letI : Algebra A A := φ.toRingHom.toAlgebra
    letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
    letI : Module A A := Algebra.toModule
    ∃ (m B R : ℕ), m = Module.finrank A A ∧ ∀ N : ℕ,
      (m * Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal N) ≤
        Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal (f.degree * N + B))) ∧
      (Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal N) ≤
        m * Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal
          ((f.degree * R + N) / f.degree))) := by
  classical
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveCoordinateDomainMap f V hq hf hV
  letI : Algebra A A := φ.toRingHom.toAlgebra
  letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
  letI : Module A A := Algebra.toModule
  obtain ⟨m, b, r, hm, hhom, hli, hr, hden⟩ :=
    projectiveCoordinateDomainMap_exists_homogeneous_generic_control f V hq hf hV
  choose d hd using hhom
  let B := Finset.univ.sup d
  have hb : ∀ i, b i ∈ homogeneousQuotientFiltration V.ideal.toIdeal B := by
    intro i
    have hdi : d i ≤ B := Finset.le_sup (Finset.mem_univ i)
    exact Finset.le_sup (f := homogeneousQuotientPiece V.ideal.toIdeal)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hdi)) (hd i)
  obtain ⟨H, hH⟩ := Ideal.Quotient.mk_surjective r
  have hrR : r ∈ homogeneousQuotientFiltration V.ideal.toIdeal H.totalDegree :=
    (homogeneousQuotientFiltration_mem_iff V.ideal.toIdeal H.totalDegree r).mpr ⟨H, le_rfl, hH⟩
  refine ⟨m, B, H.totalDegree, hm, ?_⟩
  intro N
  exact ⟨projectiveFilteredCombination_finrank_lower f V hq hf hV b hli N B hb,
    projectiveCoordinateFiltration_generic_upper f V hq hf hV b d hd hli r hr
      H.totalDegree hrR hden N⟩

end LinearStudy
