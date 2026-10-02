module

public import Negativity.IntegralCurveProjection
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
noncomputable section

/-- Final theorem: the actual complete-integral-curve projection formula
for arbitrary real Cartier combinations. Original curves may be nonnormal,
the ambient curve map need not be dominant, and the full function-field
degree includes inseparable morphisms in arbitrary characteristic. -/
theorem complete_integral_curve_real_cartier_projection
    {C Y X : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    (hdC : Order.krullDim C = 1) (hdY : Order.krullDim Y = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [IsProper b]
    (f : C ⟶ Y) [IsProper f] [IsDominant f] (j : Y ⟶ X)
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    letI : Algebra Y.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
    normalizedRealCartierCurveIntersection hdC k (f ≫ b) (f ≫ j) A r =
      (Module.finrank Y.functionField C.functionField : ℝ) *
        normalizedRealCartierCurveIntersection hdY k b j A r := by
  classical
  let : Algebra Y.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
  unfold normalizedRealCartierCurveIntersection
  simp_rw [complete_integral_curve_cartier_projection hdC hdY k b f j]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

end
end Negativity
