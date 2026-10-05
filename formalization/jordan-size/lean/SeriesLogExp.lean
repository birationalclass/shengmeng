import Mathlib.RingTheory.PowerSeries.Log

/-!
The formal power-series inverse identities supplied by mathlib.
This is a prerequisite for Lemma 1.1, not yet the finite-operator
evaluation of those identities. Coefficients are rational, irrespective
of the characteristic of a geometric base field.
-/

namespace JordanSize

/-- Formal exponential and logarithm are compositional inverses over Q.
Evaluation at a nilpotent operator remains a separate bridge. -/
theorem seriesLogExp :
    (PowerSeries.exp ℚ).subst (PowerSeries.log ℚ) =
        1 + (PowerSeries.X : PowerSeries ℚ) ∧
    (PowerSeries.log ℚ).subst (PowerSeries.exp ℚ - 1) =
        (PowerSeries.X : PowerSeries ℚ) := by
  exact ⟨PowerSeries.subst_exp_log ℚ, PowerSeries.subst_log_exp_sub_one ℚ⟩

end JordanSize

#print axioms JordanSize.seriesLogExp
