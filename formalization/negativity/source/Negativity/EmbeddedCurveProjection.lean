module

public import Negativity.ActualProjectionFormula
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Function.locallyFinsuppWithin
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- An actual closed curve embedding does not alter the residue degree
of the subsequent map to the ambient target. -/
theorem residueDegree_precomp_closedImmersion {C Y X : Scheme.{u}}
    (g : C ⟶ Y) [IsClosedImmersion g] (p : Y ⟶ X) (x : C) :
    p.residueDegree (g x) = (g ≫ p).residueDegree x := by
  let : Algebra (X.residueField (p (g x))) (Y.residueField (g x)) :=
    (p.residueFieldMap (g x)).hom.toAlgebra
  let : Algebra (X.residueField (p (g x))) (C.residueField x) :=
    ((g ≫ p).residueFieldMap x).hom.toAlgebra
  let e := RingEquiv.ofBijective (g.residueFieldMap x).hom
    (closedImmersion_residueFieldMap_bijective g x)
  change Module.finrank (X.residueField (p (g x))) (Y.residueField (g x)) =
    Module.finrank (X.residueField (p (g x))) (C.residueField x)
  apply Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _) e
  change ((g ≫ p).residueFieldMap x).hom =
    (p.residueFieldMap (g x) ≫ g.residueFieldMap x).hom
  rw [Scheme.residueFieldMap_comp]

/-- The actual ambient pushforward of the embedded curve is the actual
pushforward of its source fundamental cycle. -/
theorem embedded_curve_actual_cycle_push {C Y X : Scheme.{u}}
    (g : C ⟶ Y) [IsClosedImmersion g] (p : Y ⟶ X) [QuasiCompact p]
    (x : C) [DecidableEq C] [DecidableEq Y] [DecidableEq X] :
    AlgebraicCycle.map p Order.height Order.height (single (g x) (1 : ℝ)) =
      AlgebraicCycle.map (g ≫ p) Order.height Order.height (single x (1 : ℝ)) := by
  rw [scheme_cycle_map_single, scheme_cycle_map_single]
  simp only [AlgebraicCycle.mapCoeff, ← closedImmersion_height_eq g x,
    Scheme.Hom.comp_apply, residueDegree_precomp_closedImmersion g p x]

/-- Final theorem: (p*D).C = D.p_*[C] for an actual embedded complete
integral curve C, the actual ambient cycle pushforward under p, and
arbitrary real Cartier coefficients. All geometric image and local-order
compatibilities are proved. -/
theorem exists_embedded_complete_curve_real_projection_formula
    {C Y X : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    (hdC : Order.krullDim C = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
    (p : Y ⟶ X) [IsDominant p] [QuasiCompact p]
    (g : C ⟶ Y) [IsClosedImmersion g] [IsProper ((g ≫ p) ≫ b)]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    letI : DecidableEq Y := Classical.decEq Y
    letI : DecidableEq X := Classical.decEq X
    ∃ P : τ → CartierAtlas Y Y,
      (∀ t y, (P t).chart y ≤ p ⁻¹ᵁ (A t).chart ((A t).covers (p y)).choose ∧
        y ∈ (P t).chart y ∧ (P t).equation y = Units.map (dominantFunctionFieldMap p).toMonoidHom
          ((A t).equation ((A t).covers (p y)).choose)) ∧
      normalizedRealCartierCurveIntersection hdC k ((g ≫ p) ≫ b) g P r =
        (AlgebraicCycle.map p Order.height Order.height (single (g (genericPoint C)) (1 : ℝ)))
          ((g ≫ p) (genericPoint C)) *
            actualImageRealCartierIntersection hdC k b (g ≫ p) A r := by
  classical
  obtain ⟨P, hP, hI⟩ := exists_complete_integral_curve_actual_real_projection_formula
    hdC k b p g A r
  refine ⟨P, hP, ?_⟩
  rw [embedded_curve_actual_cycle_push g p (genericPoint C)]
  exact hI

end
end Negativity
