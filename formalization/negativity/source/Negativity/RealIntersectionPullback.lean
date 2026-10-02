module

public import Negativity.CurveIntersectionPullback
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
noncomputable section

/-- Actual real Cartier intersection vanishes for a complete normal
curve whose actual image is a single point, with arbitrary real weights. -/
theorem complete_normal_curve_real_cartier_intersection_point_image_zero
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) (hpoint : ∀ x : C, f x = f (genericPoint C))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    realCartierCurveIntersection hn f A r = 0 := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  unfold realCartierCurveIntersection
  apply Finset.sum_eq_zero
  intro t _
  rw [(complete_normal_curve_cartier_intersection_wellDefined hn hd k c f (A t)).2 hpoint]
  simp

/-- Final theorem: the actual real Cartier intersection commutes with
genuine ambient dominant pullback. All termwise Cartier pullback charts
and equations are constructed as outputs; real weights have no sign or
separability restrictions. This is the pullback composition step, not
an assertion that the full negativity lemma is finished. -/
theorem exists_complete_curve_real_cartier_intersection_pullback
    {C Y X : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (p : Y ⟶ X) [IsDominant p] (g : C ⟶ Y)
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    ∃ P : τ → CartierAtlas Y Y,
      (∀ t y, (P t).chart y ≤ p ⁻¹ᵁ (A t).chart ((A t).covers (p y)).choose ∧
        y ∈ (P t).chart y ∧ (P t).equation y = Units.map (dominantFunctionFieldMap p).toMonoidHom
          ((A t).equation ((A t).covers (p y)).choose)) ∧
      realCartierCurveIntersection hn g P r = realCartierCurveIntersection hn (g ≫ p) A r := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  choose P hP hI using fun t => exists_complete_curve_cartier_intersection_pullback
    hn hd k c p g (A t)
  refine ⟨P, hP, ?_⟩
  unfold realCartierCurveIntersection
  simp_rw [hI]

end
end Negativity
