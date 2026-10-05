import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Tactic

/-!
The finite exponential portion of Lemma 1.1, reusing mathlib's
nilpotent exponential rather than defining a second exponential.
The scalar field here is rational and independent of a geometric base field.
Main theorem: `nilpotentFlow`.
-/

noncomputable section
namespace JordanSize
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def flow (D : Module.End ℚ V) (t : ℚ) : Module.End ℚ V :=
  IsNilpotent.exp (t • D)

lemma flow_add (D : Module.End ℚ V) (hD : IsNilpotent D) (s t : ℚ) :
    flow D (s+t) = flow D s * flow D t := by
  unfold flow
  rw [add_smul]
  exact IsNilpotent.exp_add_of_commute
    (((Commute.refl D).smul_left s).smul_right t) (hD.smul s) (hD.smul t)

lemma flow_nat (D : Module.End ℚ V) (hD : IsNilpotent D) (m : ℕ) :
    flow D (m : ℚ) = (flow D 1)^m := by
  induction m with
  | zero => simp [flow]
  | succ m ih =>
    rw [Nat.cast_add_one, flow_add D hD, ih, pow_succ]

/-- All flow and positive-integer power identities in the finite exponential.
The inverse is exhibited by the negative parameter, with no analytic hypotheses. -/
theorem nilpotentFlow (D : Module.End ℚ V) (hD : IsNilpotent D) :
    flow D 0 = 1 ∧
    (∀ s t : ℚ, flow D (s+t) = flow D s * flow D t) ∧
    (∀ t : ℚ, IsUnit (flow D t)) ∧
    (∀ t : ℚ, flow D t * flow D (-t) = 1 ∧ flow D (-t) * flow D t = 1) ∧
    (∀ m : ℕ, flow D (m : ℚ) = (flow D 1)^m) := by
  refine ⟨by simp [flow], flow_add D hD, ?_, ?_, flow_nat D hD⟩
  · intro t
    exact IsNilpotent.isUnit_exp (hD.smul t)
  · intro t
    constructor
    · simpa [flow] using (flow_add D hD t (-t)).symm
    · simpa [flow] using (flow_add D hD (-t) t).symm

end JordanSize
#print axioms JordanSize.nilpotentFlow
