module
public import Linear.PolynomialGrowthRank
public import Linear.ProjectiveGenericGrowthComparison
public import Linear.ProjectiveCoordinateHilbertGrowth
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
open Filter
open scoped Topology
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem projective_coordinate_filtration_finrank_pos
    (V : IntegralProjectiveEquations n) (N : ℕ) :
    0 < Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal N) := by
  rw [homogeneousQuotientFiltration_finrank V.ideal.toIdeal V.ideal.isHomogeneous N]
  apply (projective_coordinate_hilbert_pos V 0).trans_le
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)

/-- The ORIGINAL cone pullback rank is the q-power of the degree of its
ACTUAL cumulative Hilbert polynomial. The Hilbert function is fixed by V. -/
theorem projectiveCoordinateDomainMap_rank_eq_growth_power
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (C : Polynomial ℚ) (hC : C ≠ 0)
    (hCgrowth : ∃ K : ℕ, ∀ N > K, C.eval (N : ℚ) =
      (Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal N) : ℚ)) :
    let A := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveCoordinateDomainMap f V hq hf hV
    letI : Algebra A A := φ.toRingHom.toAlgebra
    letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
    letI : Module A A := Algebra.toModule
    Module.finrank A A = f.degree ^ C.natDegree := by
  classical
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveCoordinateDomainMap f V hq hf hV
  letI : Algebra A A := φ.toRingHom.toAlgebra
  letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
  letI : Module A A := Algebra.toModule
  change Module.finrank A A = f.degree ^ C.natDegree
  obtain ⟨m, B, R, hm, hb⟩ :=
    projectiveCoordinateDomainMap_generic_growth_comparison f V hq hf hV
  rw [← hm]
  obtain ⟨K, hK⟩ := hCgrowth
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < C.eval (N : ℚ) := by
    filter_upwards [eventually_gt_atTop K] with N hn
    rw [hK N hn]
    exact_mod_cast projective_coordinate_filtration_finrank_pos V N
  apply polynomial_nat_two_sided_growth_rank C hC f.degree m B R hq hpos
  · filter_upwards [eventually_gt_atTop K] with N hn
    have hqN : N ≤ f.degree * N := by nlinarith
    have he : C.eval ((f.degree : ℚ) * N + B) =
        (Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal
          (f.degree * N + B)) : ℚ) := by
      simpa only [Nat.cast_add, Nat.cast_mul] using
        hK (f.degree * N + B) (by omega)
    rw [hK N hn, he]
    exact_mod_cast (hb N).1
  · filter_upwards [eventually_gt_atTop K] with N hn
    have hqN : N ≤ f.degree * N := by nlinarith
    have he1 : C.eval ((f.degree : ℚ) * N) =
        (Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal
          (f.degree * N)) : ℚ) := by
      simpa only [Nat.cast_mul] using hK (f.degree * N) (by omega)
    have he2 : C.eval ((N : ℚ) + R) =
        (Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal (N + R)) : ℚ) := by
      simpa only [Nat.cast_add] using hK (N + R) (by omega)
    have hu := (hb (f.degree * N)).2
    rw [← Nat.mul_add, Nat.mul_div_cancel_left _ hq, Nat.add_comm R N] at hu
    rw [he1, he2]
    exact_mod_cast hu

/-- Derive the Hilbert polynomials AND the original cone rank power from
only the original projective equations and map; no growth/rank formula input. -/
theorem projectiveCoordinateDomainMap_exists_hilbert_rank_power
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    let A := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveCoordinateDomainMap f V hq hf hV
    letI : Algebra A A := φ.toRingHom.toAlgebra
    letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
    letI : Module A A := Algebra.toModule
    ∃ P C : Polynomial ℚ, P ≠ 0 ∧ C ≠ 0 ∧ P.natDegree ≤ n ∧
      C.natDegree = P.natDegree + 1 ∧ Module.finrank A A = f.degree ^ C.natDegree ∧
      ∃ K : ℕ, ∀ N > K,
        P.eval (N : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal N : ℚ) ∧
        C.eval (N : ℚ) =
          (Module.finrank ℂ (homogeneousQuotientFiltration V.ideal.toIdeal N) : ℚ) := by
  obtain ⟨P, C, hP, hC, hdeg, hCdeg, K, hK⟩ := projective_coordinate_hilbertPolynomial_growth V
  exact ⟨P, C, hP, hC, hdeg, hCdeg,
    projectiveCoordinateDomainMap_rank_eq_growth_power f V hq hf hV C hC
      ⟨K, fun N hn => (hK N hn).2⟩, K, hK⟩

end LinearStudy
