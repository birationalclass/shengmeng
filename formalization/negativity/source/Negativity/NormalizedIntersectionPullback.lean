module

public import Negativity.NormalizedCurveIntersection
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: genuine ambient Cartier pullback commutes with
intersection on every actual complete integral curve, including singular
nonnormal curves. The actual termwise pullbacks are constructed. -/
theorem exists_complete_integral_curve_real_intersection_pullback
    {C Y X : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (p : Y ⟶ X) [IsDominant p] (g : C ⟶ Y)
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    ∃ P : τ → CartierAtlas Y Y,
      (∀ t y, (P t).chart y ≤ p ⁻¹ᵁ (A t).chart ((A t).covers (p y)).choose ∧
        y ∈ (P t).chart y ∧ (P t).equation y = Units.map (dominantFunctionFieldMap p).toMonoidHom
          ((A t).equation ((A t).covers (p y)).choose)) ∧
      normalizedRealCartierCurveIntersection hd k c g P r =
        normalizedRealCartierCurveIntersection hd k c (g ≫ p) A r := by
  let n := C.fromSpecStalk (genericPoint C)
  have h := complete_integral_curve_normalization_properties C hd k c
  have : IsLocallyNoetherian n.normalization := h.2.2.2.2.2.1
  have : IsProper (n.fromNormalization ≫ c) := h.2.2.2.2.2.2
  let : CompactSpace n.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (n.fromNormalization ≫ c)
  obtain ⟨P, hP, hI⟩ := exists_complete_curve_real_cartier_intersection_pullback
    (generic_normalization_stalks_normal C) h.2.2.2.2.1 k
    (n.fromNormalization ≫ c) p (n.fromNormalization ≫ g) A r
  refine ⟨P, hP, ?_⟩
  simpa only [normalizedRealCartierCurveIntersection, normalizedCartierCurveIntersection,
    realCartierCurveIntersection, Category.assoc] using hI

end
end Negativity
