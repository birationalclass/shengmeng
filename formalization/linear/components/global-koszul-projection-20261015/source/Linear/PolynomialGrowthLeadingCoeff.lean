module
public import Linear.PolynomialGrowthRank
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy
open Filter Polynomial
open scoped Topology

/-- Two distinct growth polynomials: a fixed shift preserves their leading-term ratio. -/
theorem polynomial_nat_shifted_ratio_tendsto
    (P Q : Polynomial ℚ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hd : Q.natDegree = P.natDegree) (B : ℕ) :
    Tendsto (fun N : ℕ => Q.eval ((N : ℚ) + B) / P.eval (N : ℚ))
      atTop (𝓝 (Q.leadingCoeff / P.leadingCoeff)) := by
  let S : Polynomial ℚ := Q.comp (C (1 : ℚ) * X + C (B : ℚ))
  have hSdeg : S.natDegree = Q.natDegree := by
    simp only [S, Polynomial.natDegree_comp,
      Polynomial.natDegree_linear (by norm_num : (1 : ℚ) ≠ 0), mul_one]
  have hSlc : S.leadingCoeff = Q.leadingCoeff := by
    change (Q.comp (C (1 : ℚ) * X + C (B : ℚ))).leadingCoeff = _
    rw [Polynomial.leadingCoeff_comp
      (by rw [Polynomial.natDegree_linear (by norm_num : (1 : ℚ) ≠ 0)]; decide),
      Polynomial.leadingCoeff_linear (by norm_num : (1 : ℚ) ≠ 0)]
    simp only [one_pow, mul_one]
  have hS : S ≠ 0 := by
    rw [← Polynomial.leadingCoeff_ne_zero, hSlc]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hdegree : S.degree = P.degree := by
    rw [Polynomial.degree_eq_natDegree hS, Polynomial.degree_eq_natDegree hP,
      hSdeg, hd]
  have hlim := (S.div_tendsto_atTop_leadingCoeff_div_of_degree_eq P hdegree).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℚ)) atTop atTop)
  rw [hSlc] at hlim
  change Tendsto (fun N : ℕ => S.eval (N : ℚ) / P.eval (N : ℚ)) atTop _ at hlim
  simpa only [S, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, one_mul] using hlim

/-- The upper-bound ratio with a shifted source polynomial. -/
theorem polynomial_nat_denominator_shift_ratio_tendsto
    (P Q : Polynomial ℚ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hd : Q.natDegree = P.natDegree) (B : ℕ) :
    Tendsto (fun N : ℕ => Q.eval (N : ℚ) / P.eval ((N : ℚ) + B))
      atTop (𝓝 (Q.leadingCoeff / P.leadingCoeff)) := by
  have h1 := polynomial_nat_shifted_ratio_tendsto P Q hP hQ hd 0
  simp only [Nat.cast_zero, add_zero] at h1
  have h2 := polynomial_nat_affine_ratio_tendsto P hP 1 B (by decide)
  simp only [Nat.cast_one, one_mul, one_pow] at h2
  have hlim := h1.div h2 (by norm_num : (1 : ℚ) ≠ 0)
  simp only [div_one] at hlim
  have hne : ∀ᶠ N : ℕ in atTop, P.eval (N : ℚ) ≠ 0 := by
    simpa only [Polynomial.IsRoot] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℚ)) atTop atTop).eventually
        (P.eventually_atTop_not_isRoot hP)
  apply hlim.congr'
  filter_upwards [hne] with N hN
  exact div_div_div_cancel_right₀ hN _ _

/-- Actual two-sided filtered growth identifies rank with a leading-coefficient ratio. -/
theorem polynomial_two_sided_growth_leadingCoeff
    (P Q : Polynomial ℚ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hd : Q.natDegree = P.natDegree) (m B E : ℕ)
    (hpos : ∀ᶠ N : ℕ in atTop, 0 < P.eval (N : ℚ))
    (hlow : ∀ᶠ N : ℕ in atTop,
      (m : ℚ) * P.eval (N : ℚ) ≤ Q.eval ((N : ℚ) + B))
    (hupp : ∀ᶠ N : ℕ in atTop,
      Q.eval (N : ℚ) ≤ (m : ℚ) * P.eval ((N : ℚ) + E)) :
    Q.leadingCoeff = (m : ℚ) * P.leadingCoeff := by
  have hlo : (m : ℚ) ≤ Q.leadingCoeff / P.leadingCoeff := by
    apply ge_of_tendsto (polynomial_nat_shifted_ratio_tendsto P Q hP hQ hd B)
    filter_upwards [hpos, hlow] with N hp hl
    exact (le_div_iff₀ hp).mpr hl
  have hshiftpos : ∀ᶠ N : ℕ in atTop, 0 < P.eval ((N : ℚ) + E) := by
    obtain ⟨K, hK⟩ := eventually_atTop.mp hpos
    filter_upwards [eventually_ge_atTop K] with N hn
    simpa only [Nat.cast_add] using hK (N + E) (by omega)
  have hup : Q.leadingCoeff / P.leadingCoeff ≤ (m : ℚ) := by
    apply le_of_tendsto (polynomial_nat_denominator_shift_ratio_tendsto P Q hP hQ hd E)
    filter_upwards [hshiftpos, hupp] with N hp hu
    exact (div_le_iff₀ hp).mpr hu
  have hratio := le_antisymm hlo hup
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  exact (div_eq_iff hlc).mp hratio.symm

end LinearStudy
