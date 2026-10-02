module

public import Negativity.RealIntegralCurveProjection
public import Negativity.Projection
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Function.locallyFinsuppWithin
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Generic residue-field multiplicity is the actual function-field degree. -/
theorem dominant_generic_residueDegree_functionField
    {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (f : C ⟶ Y) [IsDominant f] :
    letI : Algebra Y.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
    f.residueDegree (genericPoint C) = Module.finrank Y.functionField C.functionField := by
  let : Algebra Y.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
  let : Algebra (Y.residueField (f (genericPoint C))) (C.residueField (genericPoint C)) :=
    (f.residueFieldMap (genericPoint C)).hom.toAlgebra
  let rY : Y.functionField ⟶ Y.residueField (f (genericPoint C)) :=
    (Y.presheaf.stalkCongr (.of_eq (dominant_genericPoint_eq f))).inv ≫
      Y.residue (f (genericPoint C))
  have hrY : Function.Bijective rY := ⟨rY.hom.injective,
    (Y.residue_surjective _).comp (ConcreteCategory.bijective_of_isIso
      (Y.presheaf.stalkCongr (.of_eq (dominant_genericPoint_eq f))).inv).surjective⟩
  let eY := RingEquiv.ofBijective rY.hom hrY
  let eC := RingEquiv.ofBijective (C.residue (genericPoint C)).hom
    ⟨(C.residue (genericPoint C)).hom.injective, C.residue_surjective _⟩
  symm
  apply Algebra.finrank_eq_of_equiv_equiv eY eC
  change (rY ≫ f.residueFieldMap (genericPoint C)).hom =
    (CommRingCat.ofHom (dominantFunctionFieldMap f) ≫ C.residue (genericPoint C)).hom
  dsimp only [rY]
  rw [Category.assoc, Scheme.residue_residueFieldMap]
  rfl

/-- Actual dimension weights of curve generic points agree. -/
theorem curve_generic_height_preserved
    {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (hdC : Order.krullDim C = 1) (hdY : Order.krullDim Y = 1)
    (f : C ⟶ Y) [IsDominant f] :
    Order.height (genericPoint C) = Order.height (f (genericPoint C)) := by
  rw [dominant_genericPoint_eq f]
  apply WithBot.coe_injective
  change (Order.height (⊤ : C) : WithBot ℕ∞) = (Order.height (⊤ : Y) : WithBot ℕ∞)
  rw [Order.height_top_eq_krullDim, Order.height_top_eq_krullDim, hdC, hdY]

/-- Final theorem: actual mathlib cycle pushforward and actual real
Cartier intersection agree for the fundamental cycle of any complete
integral curve under a proper dominant map. We use actual dimension
weights and derive the pushforward multiplicity from generic residue
fields. No intersection compatibility identity is assumed. -/
theorem complete_integral_curve_actual_cycle_projection
    {C Y X : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    (hdC : Order.krullDim C = 1) (hdY : Order.krullDim Y = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [IsProper b]
    (f : C ⟶ Y) [IsProper f] [IsDominant f] (j : Y ⟶ X)
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    letI : Algebra Y.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableEq Y := Classical.decEq Y
    let pushed := AlgebraicCycle.map f Order.height Order.height (single (genericPoint C) (1 : ℝ))
    pushed = single (genericPoint Y) (Module.finrank Y.functionField C.functionField : ℝ) ∧
      normalizedRealCartierCurveIntersection hdC k (f ≫ b) (f ≫ j) A r =
        pushed (genericPoint Y) * normalizedRealCartierCurveIntersection hdY k b j A r := by
  classical
  let : Algebra Y.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
  have hpush : AlgebraicCycle.map f Order.height Order.height (single (genericPoint C) (1 : ℝ)) =
      single (genericPoint Y) (Module.finrank Y.functionField C.functionField : ℝ) := by
    rw [scheme_cycle_map_single,
      scheme_mapCoeff_of_same_weight f Order.height Order.height (genericPoint C)
        (curve_generic_height_preserved hdC hdY f),
      dominant_generic_residueDegree_functionField f, dominant_genericPoint_eq f, one_mul]
  refine ⟨hpush, ?_⟩
  rw [hpush]
  simp only [single_apply]
  exact complete_integral_curve_real_cartier_projection hdC hdY k b f j A r

end
end Negativity
