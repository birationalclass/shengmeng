module

public import Negativity.AdicApproximationComparison
import Mathlib.Tactic

@[expose] public section
namespace Negativity
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final algebraic theorem: the uniform kernel bound alone proves
injectivity of the canonical completion comparison. No eventual image
lifting or surjectivity hypothesis is used in this half of the proof. -/
theorem adic_comparison_injective_of_uniform_kernel_bound
    {R : Type u} [CommRing R] (I : Ideal R)
    (B : ℕ → Type v) [∀ n, CommRing (B n)]
    (t : ∀ {m n : ℕ}, m ≤ n → (B n →+* B m))
    (q : ∀ n, (R ⧸ I ^ (n + 1)) →+* B n)
    (htq : ∀ {m n : ℕ} (h : m ≤ n) (a : R ⧸ I ^ (n + 1)),
      t h (q n a) = q m (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) a))
    (c : ℕ)
    (hker : ∀ n (r : R), q (n + c) (Ideal.Quotient.mk _ r) = 0 →
      r ∈ I ^ (n + 1)) :
    Function.Injective (adicApproximationComparison I B t q htq) := by
  let P := adicApproximationComparison I B t q htq
  intro a b hab
  have hz : P (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have he : ∀ n, q n (AdicCompletion.evalₐ I (n + 1) (a - b)) = 0 := by
    intro n
    exact congrArg (fun x : compatibleRingElements B t => x.1 n) hz
  have hab0 : a - b = 0 := by
    apply AdicCompletion.ext_evalₐ
    intro n
    cases n with
    | zero =>
      have : Subsingleton (R ⧸ I ^ 0) := by simp [pow_zero]
      exact Subsingleton.elim _ _
    | succ n =>
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ I (n + c + 1) (a - b))
      have hk : r ∈ I ^ (n + 1) := hker n r (by rw [hr]; exact he (n + c))
      have hp := adic_completion_power_eval_transition I
        (show n + 1 ≤ n + c + 1 by omega) (a - b)
      rw [← hr] at hp
      change Ideal.Quotient.mk (I ^ (n + 1)) r =
        AdicCompletion.evalₐ I (n + 1) (a - b) at hp
      rw [← hp, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hk
  exact sub_eq_zero.mp hab0

end
end Negativity
