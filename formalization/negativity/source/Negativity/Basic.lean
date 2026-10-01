module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

public section

namespace Negativity

/-- A small installation check for the final numerical contradiction.
This is not the geometric negativity lemma. -/
theorem numerical_contradiction (d e a : ℝ)
    (hd : d ≤ 0) (he : 0 < e) (ha : a < 0)
    (h : 0 ≤ d + e * a) : False := by
  have hmul : e * a < 0 := mul_neg_of_pos_of_neg he ha
  linarith

end Negativity
