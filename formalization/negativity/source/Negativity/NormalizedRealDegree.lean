module

public import Negativity.NormalizedCurveDegree
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
noncomputable section

/-- Final theorem: the genuine real Cartier degree formula on every
complete integral source curve, using its constructed finite normalization.
The degree on the right is the full degree of the original function fields,
and may include an inseparable part in arbitrary characteristic. -/
theorem complete_integral_curve_real_cartier_intersection_degree
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian X]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdC : Order.krullDim C = 1) (hdX : Order.krullDim X = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) [IsProper b]
    (f : C ⟶ X) [IsProper f] [IsDominant f]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace b
    letI : Algebra X.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
    normalizedRealCartierCurveIntersection hdC k (f ≫ b) f A r =
      (Module.finrank X.functionField C.functionField : ℝ) *
        ∑ t, r t * (cartierTotalOrder X hnX (A t) : ℝ) := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace b
  let : Algebra X.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
  unfold normalizedRealCartierCurveIntersection
  simp_rw [complete_integral_curve_cartier_intersection_degree hnX hdC hdX k b f]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

end
end Negativity
