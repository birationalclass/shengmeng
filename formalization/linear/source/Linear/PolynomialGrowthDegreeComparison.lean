module
public import Linear.PolynomialGrowthLimits
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open Filter Polynomial
open scoped Topology

/-- ACTUAL eventual inequalities on natural inputs compare polynomial
degrees. The proof uses a vanishing ratio and proves that the majorant is
nonzero; no degree or asymptotic comparison is assumed. -/
theorem polynomial_natDegree_le_of_eventually_le
    (P Q : Polynomial ℚ) (hP : P ≠ 0)
    (hpos : ∀ᶠ N : ℕ in atTop, 0 < P.eval (N : ℚ))
    (hle : ∀ᶠ N : ℕ in atTop, P.eval (N : ℚ) ≤ Q.eval (N : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  have hQ : Q ≠ 0 := by
    intro hz
    have he : ∀ᶠ N : ℕ in atTop, False := by
      filter_upwards [hpos, hle] with N hp hN
      simp only [hz, Polynomial.eval_zero] at hN
      exact (not_lt_of_ge hN) hp
    exact he.exists.elim (fun _ hn => hn)
  by_contra hn
  have hdeg : Q.degree < P.degree := by
    rw [Polynomial.degree_eq_natDegree hQ, Polynomial.degree_eq_natDegree hP]
    exact_mod_cast lt_of_not_ge hn
  have hlim := (Q.div_tendsto_atTop_zero_of_degree_lt P hdeg).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℚ)) atTop atTop)
  have he : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [hpos, hle, hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℚ) < 1))]
      with N hp hN hsmall
    have hge : 1 ≤ Q.eval (N : ℚ) / P.eval (N : ℚ) :=
      (le_div_iff₀ hp).mpr (by simpa using hN)
    exact (not_lt_of_ge hge) hsmall
  exact he.exists.elim (fun _ hn => hn)

end LinearStudy
