module
public import Linear.PolynomialGrowthLimits
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy
open Filter Polynomial
open scoped Topology

/-- Fixed shifts do not change the scaled leading-term ratio. -/
theorem polynomial_nat_scaled_shift_ratio_tendsto
    (P : Polynomial ℚ) (hP : P ≠ 0) (q R : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => P.eval ((q : ℚ) * N) / P.eval ((N : ℚ) + R))
      atTop (𝓝 ((q : ℚ) ^ P.natDegree)) := by
  have h1 := polynomial_nat_affine_ratio_tendsto P hP q 0 hq
  have h2 := polynomial_nat_affine_ratio_tendsto P hP 1 R (by decide)
  simp only [Nat.cast_zero, add_zero] at h1
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

/-- Two-sided polynomial growth estimates force the ACTUAL multiplicity.
The power identity is proved by limits, not supplied as input. -/
theorem polynomial_nat_two_sided_growth_rank
    (P : Polynomial ℚ) (hP : P ≠ 0) (q m B R : ℕ) (hq : 0 < q)
    (hpos : ∀ᶠ N : ℕ in atTop, 0 < P.eval (N : ℚ))
    (hlow : ∀ᶠ N : ℕ in atTop,
      (m : ℚ) * P.eval (N : ℚ) ≤ P.eval ((q : ℚ) * N + B))
    (hupp : ∀ᶠ N : ℕ in atTop,
      P.eval ((q : ℚ) * N) ≤ (m : ℚ) * P.eval ((N : ℚ) + R)) :
    m = q ^ P.natDegree := by
  have hlo : (m : ℚ) ≤ (q : ℚ) ^ P.natDegree := by
    apply ge_of_tendsto (polynomial_nat_affine_ratio_tendsto P hP q B hq)
    filter_upwards [hpos, hlow] with N hp hl
    exact (le_div_iff₀ hp).mpr hl
  have hshiftpos : ∀ᶠ N : ℕ in atTop, 0 < P.eval ((N : ℚ) + R) := by
    obtain ⟨K, hK⟩ := eventually_atTop.mp hpos
    filter_upwards [eventually_ge_atTop K] with N hn
    simpa only [Nat.cast_add] using hK (N + R) (by omega)
  have hup : (q : ℚ) ^ P.natDegree ≤ (m : ℚ) := by
    apply le_of_tendsto (polynomial_nat_scaled_shift_ratio_tendsto P hP q R hq)
    filter_upwards [hshiftpos, hupp] with N hp hu
    exact (div_le_iff₀ hp).mpr hu
  exact_mod_cast le_antisymm hlo hup

end LinearStudy
