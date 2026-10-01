module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

@[expose] public section

namespace Negativity

/-- Effectivity of a finitely supported real coefficient vector. -/
def Effective {I : Type*} (d : I →₀ ℝ) : Prop := ∀ i, 0 ≤ d i

/-- The maximum-ratio step: add a positive multiple of `a` to make `d`
effective, with a zero coefficient at an originally negative component. -/
theorem exists_effective_shift {I : Type*} (d a : I →₀ ℝ)
    (ha : Effective a) (hcover : ∀ i, d i < 0 → 0 < a i)
    (hneg : ¬ Effective d) :
    ∃ e : ℝ, 0 < e ∧ Effective (d + e • a) ∧
      ∃ j, d j < 0 ∧ (d + e • a) j = 0 := by
  classical
  have hn : ∃ i, d i < 0 := by
    simpa only [Effective, not_forall, not_le] using hneg
  let s := d.support.filter (fun i => d i < 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hn
    exact ⟨i, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (ne_of_lt hi), hi⟩⟩
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => -d i / a i) hs
  have hdj : d j < 0 := (Finset.mem_filter.mp hj).2
  have haj : 0 < a j := hcover j hdj
  let e := -d j / a j
  have he : 0 < e := div_pos (neg_pos.mpr hdj) haj
  refine ⟨e, he, ?_, j, hdj, ?_⟩
  · intro i
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hi : d i < 0
    · have hai := hcover i hi
      have his : i ∈ s := Finset.mem_filter.mpr
        ⟨Finsupp.mem_support_iff.mpr (ne_of_lt hi), hi⟩
      have hle : -d i / a i ≤ e := hmax i his
      have := (div_le_iff₀ hai).mp hle
      linarith
    · have hdi : 0 ≤ d i := le_of_not_gt hi
      exact add_nonneg hdi (mul_nonneg he.le (ha i))
  · simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    dsimp [e]
    rw [div_mul_cancel₀ _ (ne_of_gt haj)]
    ring

/-- Conditional numerical negativity. The curve-existence and intersection
properties are explicit hypotheses; no geometric results are asserted here. -/
theorem effective_of_curve_tests {I V C : Type*}
    [AddCommGroup V] [Module ℝ V]
    (coeff : V →ₗ[ℝ] (I →₀ ℝ)) (intersection : C → V →ₗ[ℝ] ℝ)
    (D E : V)
    (hE : Effective (coeff E))
    (hcover : ∀ i, coeff D i < 0 → 0 < coeff E i)
    (hnef : ∀ c, intersection c D ≤ 0)
    (hanti : ∀ c, intersection c E < 0)
    (hcurve : ∀ B j, Effective (coeff B) → coeff D j < 0 → coeff B j = 0 →
      ∃ c, 0 ≤ intersection c B) :
    Effective (coeff D) := by
  by_contra hneg
  obtain ⟨e, he, hshift, j, hj, hzero⟩ :=
    exists_effective_shift (coeff D) (coeff E) hE hcover hneg
  have hcoeff : coeff (D + e • E) = coeff D + e • coeff E := by simp
  obtain ⟨c, hc⟩ := hcurve (D + e • E) j (hcoeff.symm ▸ hshift) hj
    (by simpa only [hcoeff] using hzero)
  have hmul : e * intersection c E < 0 := mul_neg_of_pos_of_neg he (hanti c)
  have hd := hnef c
  simp only [map_add, map_smul, smul_eq_mul] at hc
  linarith

end Negativity

