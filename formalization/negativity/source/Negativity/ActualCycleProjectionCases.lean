module

public import Negativity.ActualRelativeNef
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Function.locallyFinsuppWithin
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- An actual complete curve collapsed to a point has zero actual
ambient one-cycle pushforward, with actual dimension weights. -/
theorem actual_point_image_curve_cycle_zero {C X : Scheme.{u}} [IsIntegral C]
    (hdC : Order.krullDim C = 1) (f : C ⟶ X) [IsProper f]
    (hs : Subsingleton f.image) [DecidableEq C] [DecidableEq X] :
    AlgebraicCycle.map f Order.height Order.height (single (genericPoint C) (1 : ℝ)) = 0 := by
  have : IsIntegral f.image := proper_integral_actual_image_isIntegral f
  have hC : Order.height (genericPoint C) = 1 := by
    apply WithBot.coe_injective
    change (Order.height (⊤ : C) : WithBot ℕ∞) = 1
    rw [Order.height_top_eq_krullDim, hdC]
  have hY : Order.height (f.toImage (genericPoint C)) = 0 := by
    apply Order.height_eq_zero.mpr
    intro y _
    exact (hs.elim y (f.toImage (genericPoint C))) ▸ le_refl _
  have hX : Order.height (f (genericPoint C)) = 0 := by
    have he := closedImmersion_height_eq f.imageι (f.toImage (genericPoint C))
    simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι, hY] using he.symm
  apply scheme_curve_push_of_drop f Order.height Order.height (genericPoint C)
  rw [hC, hX]
  exact one_ne_zero

/-- Final theorem: both projection cases for actual complete integral
curves, actual real Cartier intersection and actual ambient cycles.
The point image pushes to zero; the curve image pushes with the full
function-field degree. No compatibility or testability input is assumed. -/
theorem actual_complete_curve_cycle_projection_cases
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (hdC : Order.krullDim C = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
    (f : C ⟶ X) [IsProper (f ≫ b)]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    letI : IsProper f := IsProper.of_comp f b
    letI : IsIntegral f.image := proper_integral_actual_image_isIntegral f
    letI : Algebra f.image.functionField C.functionField :=
      (dominantFunctionFieldMap f.toImage).toAlgebra
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableEq X := Classical.decEq X
    let pushed := AlgebraicCycle.map f Order.height Order.height (single (genericPoint C) (1 : ℝ))
    (Subsingleton f.image ∧ pushed = 0 ∧
      normalizedRealCartierCurveIntersection hdC k (f ≫ b) f A r = 0) ∨
      (Order.krullDim f.image = 1 ∧
        pushed = single (f (genericPoint C)) (Module.finrank f.image.functionField C.functionField : ℝ) ∧
        normalizedRealCartierCurveIntersection hdC k (f ≫ b) f A r =
          (Module.finrank f.image.functionField C.functionField : ℝ) *
            actualImageRealCartierIntersection hdC k b f A r) := by
  classical
  have : IsProper f := IsProper.of_comp f b
  have : IsIntegral f.image := proper_integral_actual_image_isIntegral f
  let : Algebra f.image.functionField C.functionField :=
    (dominantFunctionFieldMap f.toImage).toAlgebra
  rcases complete_integral_curve_actual_image_dichotomy hdC k b f A r with ⟨hs, hz⟩ | hd
  · exact Or.inl ⟨hs, actual_point_image_curve_cycle_zero hdC f hs, hz⟩
  · right
    have hwt : Order.height (genericPoint C) = Order.height (f (genericPoint C)) := by
      have he := (curve_generic_height_preserved hdC hd f.toImage).trans
        (closedImmersion_height_eq f.imageι (f.toImage (genericPoint C)))
      simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] using he
    have hpush : AlgebraicCycle.map f Order.height Order.height (single (genericPoint C) (1 : ℝ)) =
        single (f (genericPoint C)) (Module.finrank f.image.functionField C.functionField : ℝ) := by
      rw [scheme_cycle_map_single,
        scheme_mapCoeff_of_same_weight f Order.height Order.height (genericPoint C) hwt,
        actual_image_residueDegree_functionField f, one_mul]
    refine ⟨hd, hpush, ?_⟩
    have hi := complete_integral_curve_ambient_real_projection hdC k b f A r
    simpa only [hpush, single_apply, ite_true] using hi

end
end Negativity
