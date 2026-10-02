module

public import Negativity.FixedCartierPullbackIntersection
public import Negativity.NormalizedIntersectionPullback
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A single actual Cartier pullback, fixed independently of test curves. -/
def actualCartierPullback {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ X) [IsDominant p] {ι : Type*} (A : CartierAtlas X ι) : CartierAtlas Y Y :=
  (exists_cartierAtlas_pullback p A).choose

theorem actualCartierPullback_data {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ X) [IsDominant p] {ι : Type*} (A : CartierAtlas X ι) (y : Y) :
    (actualCartierPullback p A).chart y ≤ p ⁻¹ᵁ A.chart (A.covers (p y)).choose ∧
      y ∈ (actualCartierPullback p A).chart y ∧
      (actualCartierPullback p A).equation y = Units.map (dominantFunctionFieldMap p).toMonoidHom
        (A.equation (A.covers (p y)).choose) :=
  (exists_cartierAtlas_pullback p A).choose_spec y

/-- Final theorem: the same fixed actual pullback has the intersection
composition formula for every complete integral test curve. The curve
may be nonnormal and its image may lie in the divisor support. -/
theorem complete_integral_curve_canonical_real_pullback_intersection
    {C Y X : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (p : Y ⟶ X) [IsDominant p] (g : C ⟶ Y)
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    normalizedRealCartierCurveIntersection hd k c g (fun t => actualCartierPullback p (A t)) r =
      normalizedRealCartierCurveIntersection hd k c (g ≫ p) A r := by
  classical
  let n := C.fromSpecStalk (genericPoint C)
  have h := complete_integral_curve_normalization_properties C hd k c
  have : IsLocallyNoetherian n.normalization := h.2.2.2.2.2.1
  have : IsProper (n.fromNormalization ≫ c) := h.2.2.2.2.2.2
  let : CompactSpace n.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (n.fromNormalization ≫ c)
  unfold normalizedRealCartierCurveIntersection normalizedCartierCurveIntersection
  apply Finset.sum_congr rfl
  intro t _
  congr 2
  have hp := complete_curve_cartier_intersection_of_actual_pullback
    (generic_normalization_stalks_normal C) h.2.2.2.2.1 k
    (n.fromNormalization ≫ c) p (n.fromNormalization ≫ g) (A t)
    (actualCartierPullback p (A t)) (actualCartierPullback_data p (A t))
  simpa only [Category.assoc] using hp

end
end Negativity
