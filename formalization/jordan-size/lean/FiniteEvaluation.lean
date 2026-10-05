import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Tactic
import SeriesEvaluation

noncomputable section
namespace JordanSize
variable {A : Type*} [CommRing A] [Algebra ℚ A]
  [UniformSpace ℚ] [DiscreteUniformity ℚ]
  [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

/-- Evaluation at a nilpotent element is a finite sum of coefficients.
There is no convergence calculation: every term beyond k vanishes. -/
theorem finiteEvaluation (a : A) (k : ℕ) (hk : a ^ k = 0)
    (hmap : Continuous (algebraMap ℚ A)) (f : PowerSeries ℚ) :
    PowerSeries.eval₂ (algebraMap ℚ A) a f =
      ∑ i ∈ Finset.range k, algebraMap ℚ A (PowerSeries.coeff i f) * a ^ i := by
  rw [PowerSeries.eval₂_eq_tsum hmap (IsNilpotent.isTopologicallyNilpotent ⟨k, hk⟩)]
  apply tsum_eq_sum
  intro i hi
  have hki : k ≤ i := Nat.le_of_not_gt (by simpa using hi)
  rw [pow_eq_zero_of_le hki hk, mul_zero]

/-- The power-series exponential agrees with mathlib's finite exponential. -/
theorem evaluatedExp_eq_finite (a : A) (ha : IsNilpotent a)
    (hmap : Continuous (algebraMap ℚ A)) :
    PowerSeries.eval₂ (algebraMap ℚ A) a (PowerSeries.exp ℚ) =
      IsNilpotent.exp a := by
  obtain ⟨k, hk⟩ := ha
  rw [finiteEvaluation a k hk hmap, IsNilpotent.exp_eq_sum hk]
  apply Finset.sum_congr rfl
  intro i hi
  simp [PowerSeries.coeff_exp, Algebra.smul_def, one_div]

/-- Likewise the logarithm is exactly its truncated rational polynomial. -/
theorem evaluatedLog_eq_finite (a : A) (k : ℕ) (hk : a ^ k = 0)
    (hmap : Continuous (algebraMap ℚ A)) :
    PowerSeries.eval₂ (algebraMap ℚ A) a (PowerSeries.log ℚ) =
      ∑ i ∈ Finset.range k,
        (if i = 0 then 0 else (-1 : ℚ) ^ (i + 1) / i) • a ^ i := by
  rw [finiteEvaluation a k hk hmap]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i = 0
  · simp [h]
  · simp [PowerSeries.coeff_log, h, Algebra.smul_def]

/-- The actual truncated logarithm, with its coefficients written out. -/
def finiteLog (a : A) (k : ℕ) : A :=
  ∑ i ∈ Finset.range k,
    (if i = 0 then 0 else (-1 : ℚ) ^ (i + 1) / i) • a ^ i

lemma finiteLog_nilpotent (a : A) (ha : IsNilpotent a) (k : ℕ) :
    IsNilpotent (finiteLog a k) := by
  apply isNilpotent_sum
  intro i hi
  by_cases h : i = 0
  · simp [h]
  · exact (ha.pow_of_pos h).smul _

/-- The formal identity is now the finite nilpotent identity. -/
theorem finiteExpLog (a : A) (k : ℕ) (hk : a ^ k = 0)
    (hmap : Continuous (algebraMap ℚ A)) :
    IsNilpotent.exp (finiteLog a k) = 1 + a := by
  have hlog : PowerSeries.eval₂ (algebraMap ℚ A) a (PowerSeries.log ℚ) =
      finiteLog a k := evaluatedLog_eq_finite a k hk hmap
  rw [← evaluatedExp_eq_finite _ (finiteLog_nilpotent a ⟨k, hk⟩ k) hmap,
    ← hlog]
  exact evaluated_exp_log a ⟨k, hk⟩ hmap

end JordanSize
#print axioms JordanSize.finiteEvaluation
#print axioms JordanSize.evaluatedExp_eq_finite
#print axioms JordanSize.evaluatedLog_eq_finite
#print axioms JordanSize.finiteExpLog
