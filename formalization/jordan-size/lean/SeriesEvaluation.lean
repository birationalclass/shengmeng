import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Tactic

/-!
Evaluation of the formal inverse identities in a commutative rational algebra.
This is an intermediate bridge, not the complete finite-operator statement.
-/

noncomputable section
namespace JordanSize
variable {A : Type*} [CommRing A] [Algebra ℚ A]
  [UniformSpace ℚ] [DiscreteUniformity ℚ]
  [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

lemma evaluated_exp_log (a : A) (ha : IsNilpotent a)
    (hmap : Continuous (algebraMap ℚ A)) :
    PowerSeries.eval₂ (algebraMap ℚ A)
      (PowerSeries.eval₂ (algebraMap ℚ A) a (PowerSeries.log ℚ))
      (PowerSeries.exp ℚ) = 1 + a := by
  have heval : PowerSeries.HasEval a := ha.isTopologicallyNilpotent
  have hsubst : PowerSeries.HasSubst (PowerSeries.log ℚ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (PowerSeries.constantCoeff_log)
  have hcomp := MvPowerSeries.eval₂_subst
    (R := ℚ) (S := ℚ) (T := A) hsubst.const
    (PowerSeries.hasEval heval) (PowerSeries.exp ℚ)
  change PowerSeries.eval₂ (algebraMap ℚ A) a
    ((PowerSeries.exp ℚ).subst (PowerSeries.log ℚ)) =
    PowerSeries.eval₂ (algebraMap ℚ A)
      (PowerSeries.eval₂ (algebraMap ℚ A) a (PowerSeries.log ℚ))
      (PowerSeries.exp ℚ) at hcomp
  rw [← hcomp, PowerSeries.subst_exp_log]
  rw [← PowerSeries.coe_eval₂Hom hmap heval, map_add, map_one]
  rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]

lemma evaluated_log_exp (a : A) (ha : IsNilpotent a)
    (hmap : Continuous (algebraMap ℚ A)) :
    PowerSeries.eval₂ (algebraMap ℚ A)
      (PowerSeries.eval₂ (algebraMap ℚ A) a (PowerSeries.exp ℚ) - 1)
      (PowerSeries.log ℚ) = a := by
  have heval : PowerSeries.HasEval a := ha.isTopologicallyNilpotent
  have hsubst : PowerSeries.HasSubst (PowerSeries.exp ℚ - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      change PowerSeries.constantCoeff (PowerSeries.exp ℚ - 1) = 0
      simp)
  have hcomp := MvPowerSeries.eval₂_subst
    (R := ℚ) (S := ℚ) (T := A) hsubst.const
    (PowerSeries.hasEval heval) (PowerSeries.log ℚ)
  change PowerSeries.eval₂ (algebraMap ℚ A) a
    ((PowerSeries.log ℚ).subst (PowerSeries.exp ℚ - 1)) =
    PowerSeries.eval₂ (algebraMap ℚ A)
      (PowerSeries.eval₂ (algebraMap ℚ A) a (PowerSeries.exp ℚ - 1))
      (PowerSeries.log ℚ) at hcomp
  have hsub : PowerSeries.eval₂ (algebraMap ℚ A) a (PowerSeries.exp ℚ - 1) =
      PowerSeries.eval₂ (algebraMap ℚ A) a (PowerSeries.exp ℚ) - 1 := by
    rw [← PowerSeries.coe_eval₂Hom hmap heval, map_sub, map_one]
  rw [← hsub, ← hcomp, PowerSeries.subst_log_exp_sub_one, PowerSeries.eval₂_X]

/-- Both inverse identities survive evaluation at a nilpotent element.
The hypotheses specify the topological evaluation API being used; the
remaining operator bridge must identify this evaluation with finite sums. -/
theorem evaluatedInverse (a : A) (ha : IsNilpotent a)
    (hmap : Continuous (algebraMap ℚ A)) :
    PowerSeries.eval₂ (algebraMap ℚ A)
      (PowerSeries.eval₂ (algebraMap ℚ A) a (PowerSeries.log ℚ))
      (PowerSeries.exp ℚ) = 1 + a ∧
    PowerSeries.eval₂ (algebraMap ℚ A)
      (PowerSeries.eval₂ (algebraMap ℚ A) a (PowerSeries.exp ℚ) - 1)
      (PowerSeries.log ℚ) = a :=
  ⟨evaluated_exp_log a ha hmap, evaluated_log_exp a ha hmap⟩

end JordanSize
#print axioms JordanSize.evaluatedInverse
