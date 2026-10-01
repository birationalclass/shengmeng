module

public import Negativity.Numerical
import Mathlib.Tactic

@[expose] public section
namespace Negativity

/-- Coefficient pushforward along an injective strict-transform map.
The existence and geometric interpretation of that map are not asserted here. -/
noncomputable def birationalPush {I J : Type*} (strict : J → I)
    (hinj : Function.Injective strict) (d : I →₀ ℝ) : J →₀ ℝ :=
  Finsupp.comapDomain strict d hinj.injOn

@[simp] theorem birationalPush_apply {I J : Type*} (strict : J → I)
    (hinj : Function.Injective strict) (d : I →₀ ℝ) (j : J) :
    birationalPush strict hinj d j = d (strict j) := rfl

/-- Indices not arising as strict transforms. -/
def ExceptionalIndex {I J : Type*} (strict : J → I) (i : I) : Prop :=
  i ∉ Set.range strict

theorem effective_push {I J : Type*} (strict : J → I)
    (hinj : Function.Injective strict) {d : I →₀ ℝ} (hd : Effective d) :
    Effective (birationalPush strict hinj d) := by
  intro j
  exact hd (strict j)

theorem negative_is_exceptional {I J : Type*} (strict : J → I)
    (hinj : Function.Injective strict) {d : I →₀ ℝ}
    (hpush : Effective (birationalPush strict hinj d)) {i : I} (hi : d i < 0) :
    ExceptionalIndex strict i := by
  rintro ⟨j, rfl⟩
  exact (not_lt_of_ge (hpush j)) hi

/-- The boundary shift is the least nonnegative effective shift. -/
theorem exists_least_effective_shift {I : Type*} (d a : I →₀ ℝ)
    (ha : Effective a) (hcover : ∀ i, d i < 0 → 0 < a i)
    (hneg : ¬ Effective d) :
    ∃ e : ℝ, 0 < e ∧
      (∀ t : ℝ, 0 ≤ t → (Effective (d + t • a) ↔ e ≤ t)) ∧
      ∃ j, d j < 0 ∧ (d + e • a) j = 0 := by
  obtain ⟨e, he, hshift, j, hj, hzero⟩ := exists_effective_shift d a ha hcover hneg
  refine ⟨e, he, ?_, j, hj, hzero⟩
  intro t _ht
  constructor
  · intro ht
    have hjpos := hcover j hj
    have htj := ht j
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at htj hzero
    nlinarith
  · intro hle i
    have hi := hshift i
    have hprod : e * a i ≤ t * a i := mul_le_mul_of_nonneg_right hle (ha i)
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hi ⊢
    linarith

end Negativity

