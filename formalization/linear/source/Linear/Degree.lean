module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Tactic

/-! # The final degree contradiction (not the geometric theorem)
The intersection lower bound is an explicit input. Its geometric construction
is not hidden in the arithmetic statement. Natural subtraction is controlled
by `1 ≤ r`. The bound `m` must be uniform before choosing the iterate.
-/

@[expose] public section
namespace LinearStudy

theorem iterate_degree_exceeds (q B : ℕ) (hq : 1 < q) :
    ∃ k : ℕ, 0 < k ∧ B < q ^ k := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B hq
  refine ⟨k + 1, Nat.succ_pos _, lt_of_lt_of_le hk ?_⟩
  exact Nat.pow_le_pow_right (by omega) (by omega)

theorem intersection_degree_lt (q r d m : ℕ) (hr : 1 ≤ r) (h : d * m < q) :
    q ^ (r - 1) * d * m < q ^ r := by
  have hq : 0 < q := by omega
  have hpow : 0 < q ^ (r - 1) := pow_pos hq _
  calc
    q ^ (r - 1) * d * m = q ^ (r - 1) * (d * m) := by ring
    _ < q ^ (r - 1) * q := Nat.mul_lt_mul_of_pos_left h hpow
    _ = q ^ r := by rw [← pow_succ]; congr 1; omega

theorem degree_contradiction (q r d m : ℕ) (hr : 1 ≤ r)
    (hlarge : d * m < q)
    (hintersection : q ^ r ≤ q ^ (r - 1) * d * m) : False := by
  exact (not_le_of_gt (intersection_degree_lt q r d m hr hlarge)) hintersection

/-- A uniform degree bound is essential: an iterate-dependent bound would
not allow the quantifiers to be exchanged. The geometric degree estimate is
still the hypothesis of this checked arithmetic reduction. -/
theorem uniform_degree_estimate_impossible (q r d : ℕ) (hq : 1 < q)
    (hr : 1 ≤ r)
    (h : ∃ m : ℕ, ∀ k : ℕ, 0 < k →
      d * m < q ^ k → (q ^ k) ^ r ≤ (q ^ k) ^ (r - 1) * d * m) : False := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨k, hk, hlarge⟩ := iterate_degree_exceeds q (d * m) hq
  exact degree_contradiction (q ^ k) r d m hr hlarge (hm k hk hlarge)

end LinearStudy
