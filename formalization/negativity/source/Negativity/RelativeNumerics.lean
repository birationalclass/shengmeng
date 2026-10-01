module

public import Negativity.Interfaces
import Mathlib.Tactic

@[expose] public section
namespace Negativity

/-- Numerical f-nefness: the quantifier ranges only over f-contracted curves. -/
def RelativeNef {V C : Type*} [AddCommGroup V] [Module ℝ V]
    (contracted : C → Prop) (degree : C → V →ₗ[ℝ] ℝ) (D : V) : Prop :=
  ∀ c, contracted c → 0 ≤ degree c D

/-- Strict positivity on contracted curves. Relative ampleness implies this
numerical property; the converse is not claimed. -/
def RelativeCurvePositive {V C : Type*} [AddCommGroup V] [Module ℝ V]
    (contracted : C → Prop) (degree : C → V →ₗ[ℝ] ℝ) (D : V) : Prop :=
  ∀ c, contracted c → 0 < degree c D

/-- The sign used in negativity is exactly the definition of relative nefness. -/
theorem relative_nef_neg_iff {V C : Type*} [AddCommGroup V] [Module ℝ V]
    (contracted : C → Prop) (degree : C → V →ₗ[ℝ] ℝ) (D : V) :
    RelativeNef contracted degree (-D) ↔ ∀ c, contracted c → degree c D ≤ 0 := by
  simp [RelativeNef]

/-- The relative strict-positive property gives the anti-ample sign only on
contracted curves. It is not used as a definition of geometric ampleness. -/
theorem relative_curvePositive_neg_iff {V C : Type*} [AddCommGroup V] [Module ℝ V]
    (contracted : C → Prop) (degree : C → V →ₗ[ℝ] ℝ) (E : V) :
    RelativeCurvePositive contracted degree (-E) ↔
      ∀ c, contracted c → degree c E < 0 := by
  simp [RelativeCurvePositive]

end Negativity
