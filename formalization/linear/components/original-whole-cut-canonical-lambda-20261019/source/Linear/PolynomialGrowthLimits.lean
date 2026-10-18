module
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Normed.Group.Rat
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy
open Filter Polynomial
open scoped Topology

/-- Polynomial ratios along NATURAL degrees use the actual leading terms. -/
theorem polynomial_nat_affine_ratio_tendsto (P : Polynomial ℚ) (hP : P ≠ 0)
    (q B : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => P.eval (q * (N : ℚ) + B) / P.eval (N : ℚ))
      atTop (𝓝 ((q : ℚ) ^ P.natDegree)) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  let Q : Polynomial ℚ := P.comp (C (q : ℚ) * X + C (B : ℚ))
  have hQdeg : Q.natDegree = P.natDegree := by
    simp only [Q, Polynomial.natDegree_comp, Polynomial.natDegree_linear hq0, mul_one]
  have hQlc : Q.leadingCoeff = P.leadingCoeff * (q : ℚ) ^ P.natDegree := by
    change (P.comp (C (q : ℚ) * X + C (B : ℚ))).leadingCoeff = _
    rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_linear hq0]; decide),
      Polynomial.leadingCoeff_linear hq0]
  have hQ : Q ≠ 0 := by
    rw [← Polynomial.leadingCoeff_ne_zero]
    rw [hQlc]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP) (pow_ne_zero _ hq0)
  have hdegree : Q.degree = P.degree := by
    rw [Polynomial.degree_eq_natDegree hQ, Polynomial.degree_eq_natDegree hP, hQdeg]
  have hlim := (Q.div_tendsto_atTop_leadingCoeff_div_of_degree_eq P hdegree).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℚ)) atTop atTop)
  have hratio : Q.leadingCoeff / P.leadingCoeff = (q : ℚ) ^ P.natDegree := by
    rw [hQlc]
    field_simp [Polynomial.leadingCoeff_ne_zero.mpr hP]
  rw [hratio] at hlim
  change Tendsto (fun N : ℕ => Q.eval (N : ℚ) / P.eval (N : ℚ)) atTop _ at hlim
  simpa only [Function.comp_apply, Q, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using hlim

/-- Strictly positive eventual values on natural degrees force a positive
leading coefficient; no leading coefficient sign is supplied. -/
theorem polynomial_leadingCoeff_pos_of_eventually_nat_pos
    (P : Polynomial ℚ) (hpos : ∀ᶠ N : ℕ in atTop, 0 < P.eval (N : ℚ)) :
    0 < P.leadingCoeff := by
  by_cases hd : P.natDegree = 0
  · obtain ⟨N, hN⟩ := hpos.exists
    have hEval : P.eval (N : ℚ) = P.leadingCoeff := by
      calc
        _ = (C (P.coeff 0)).eval (N : ℚ) := congrArg (Polynomial.eval (N : ℚ))
          (Polynomial.eq_C_of_natDegree_eq_zero hd)
        _ = P.coeff 0 := Polynomial.eval_C
        _ = P.leadingCoeff := by simp only [Polynomial.leadingCoeff, hd]
    rwa [hEval] at hN
  · by_contra hn
    have hdeg : 0 < P.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
    have hneg := (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg (le_of_not_gt hn)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℚ)) atTop atTop)
    have hfalse : ∀ᶠ N : ℕ in atTop, False := by
      filter_upwards [hpos, hneg.eventually (eventually_lt_atBot 0)] with N hp hn
      exact (not_lt_of_ge hp.le) hn
    exact hfalse.exists.elim (fun _ hn => hn)

end LinearStudy
