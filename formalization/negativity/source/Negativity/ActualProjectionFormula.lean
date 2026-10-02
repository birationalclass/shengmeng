module

public import Negativity.AmbientCurveProjection
public import Negativity.NormalizedIntersectionPullback
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Function.locallyFinsuppWithin
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: construct actual real Cartier pullbacks and prove
(p*D).C = D.p_*[C] with the actual ambient mathlib cycle map. Curve images,
normalizations, dimension drops, full residue-field degrees, local orders
and intersection compatibility are all derived. The image can be a
point or a nonnormal curve, and inseparable degrees are retained. -/
theorem exists_complete_integral_curve_actual_real_projection_formula
    {C Y X : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    (hdC : Order.krullDim C = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
    (p : Y ⟶ X) [IsDominant p] (g : C ⟶ Y) [IsProper ((g ≫ p) ≫ b)]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    letI : IsProper (g ≫ p) := IsProper.of_comp (g ≫ p) b
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableEq X := Classical.decEq X
    ∃ P : τ → CartierAtlas Y Y,
      (∀ t y, (P t).chart y ≤ p ⁻¹ᵁ (A t).chart ((A t).covers (p y)).choose ∧
        y ∈ (P t).chart y ∧ (P t).equation y = Units.map (dominantFunctionFieldMap p).toMonoidHom
          ((A t).equation ((A t).covers (p y)).choose)) ∧
      normalizedRealCartierCurveIntersection hdC k ((g ≫ p) ≫ b) g P r =
        (AlgebraicCycle.map (g ≫ p) Order.height Order.height (single (genericPoint C) (1 : ℝ)))
          ((g ≫ p) (genericPoint C)) *
            actualImageRealCartierIntersection hdC k b (g ≫ p) A r := by
  classical
  have : IsProper (g ≫ p) := IsProper.of_comp (g ≫ p) b
  obtain ⟨P, hP, hI⟩ := exists_complete_integral_curve_real_intersection_pullback
    hdC k ((g ≫ p) ≫ b) p g A r
  refine ⟨P, hP, hI.trans ?_⟩
  exact complete_integral_curve_ambient_real_projection hdC k b (g ≫ p) A r

end
end Negativity
